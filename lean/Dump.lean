/- Dump.lean -- declaration graph of a Lean project, for trust-ledger (docs/FORMAT.md).

   Usage (inside the project's Lake environment, after `lake build`):
     lake env lean --run Dump.lean module=Toy root=Toy assume=Toy.BanachProp < names.txt

   names.txt: one declaration name per line.  The dump contains these declarations and every
   project declaration (name under `root`) they depend on, transitively.  Output: one JSON object
   on stdout,
     {toolchain, decls: {name: {kind, module, line, axioms, sorry, assumptions,
                                type, type_term, value, value_term, proof_term,
                                stmt_deps, proof_deps}}}
   `type`/`value` are pretty-printed (for humans); `*_term` is an exact serialisation of the
   kernel term (binder names ignored, shared subterms numbered), which is what gets hashed.
   Auxiliary constants (`match_n`, `_proof_n`, `eq_n`, `_unary`, ...) are not nodes: their
   content is folded into the declaration that uses them.
   `assumptions`: constants listed in `assume=` that occur as hypotheses of the statement. -/
import Lean

open Lean Meta

structure Ser where
  ids : Std.HashMap Expr Nat := {}
  out : Array String := #[]

partial def ser (e : Expr) : StateM Ser Nat := do
  if let .mdata _ e' := e then return ← ser e'
  if let some i := (← get).ids[e]? then return i
  let s ← match e with
    | .bvar i => pure s!"b{i}"
    | .fvar _ | .mvar _ => pure "?"
    | .sort l => pure s!"s{toString (Std.format l)}"
    | .const n ls => pure s!"c{n}[{",".intercalate (ls.map fun l => toString (Std.format l))}]"
    | .app f a => do let i ← ser f; let j ← ser a; pure s!"a{i} {j}"
    | .lam _ t b _ => do let i ← ser t; let j ← ser b; pure s!"l{i} {j}"
    | .forallE _ t b _ => do let i ← ser t; let j ← ser b; pure s!"p{i} {j}"
    | .letE _ t v b _ => do let i ← ser t; let j ← ser v; let k ← ser b; pure s!"L{i} {j} {k}"
    | .lit (.natVal n) => pure s!"n{n}"
    | .lit (.strVal s) => pure s!"S{(Json.str s).compress}"
    | .proj n i e => do let j ← ser e; pure s!"j{n}.{i} {j}"
    | .mdata .. => pure "="  -- unreachable: stripped above
  let st ← get
  set { st with ids := st.ids.insert e st.out.size, out := st.out.push s }
  return st.out.size

/-- Exact term serialisation: numbered nodes, then the root index. -/
def serialise (e : Expr) : String :=
  let (i, st) := (ser e).run {}
  ";".intercalate st.out.toList ++ s!"|{i}"

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"

/-- `ConstantInfo.value?` skips theorems in recent Lean; do not rely on it. -/
def valueOf : ConstantInfo → Option Expr
  | .defnInfo v => some v.value | .thmInfo v => some v.value | _ => none

def ppStr (e : Expr) : MetaM String := do
  let o := (← getOptions).setBool `pp.fullNames true |>.setBool `pp.universes true
    |>.setBool `pp.proofs true
  withOptions (fun _ => o) do return toString (← ppExpr e)

structure Cfg where
  root : Name
  assume : List Name

def isProject (c : Cfg) (n : Name) : Bool := n.getRoot == c.root

/-- generated helper constants: folded into their user instead of being nodes -/
def isAux (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_"
  | _ => false

/-- project constants reachable from `cs`, auxiliary ones expanded in place.
    Returns (non-auxiliary dependencies, auxiliary constants). -/
partial def resolve (c : Cfg) (env : Environment) (cs : Array Name) :
    NameSet × NameSet := Id.run do
  let mut deps : NameSet := {}
  let mut aux : NameSet := {}
  let mut todo := cs.toList
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if !isProject c n then continue
      if isAux n then
        if aux.contains n then continue
        aux := aux.insert n
        if let some ci := env.find? n then
          todo := ci.type.getUsedConstants.toList ++ ((valueOf ci).map (·.getUsedConstants.toList) |>.getD []) ++ todo
      else deps := deps.insert n
  return (deps, aux)

def names (s : NameSet) : Array Name := s.toArray.qsort (·.toString < ·.toString)

def assumptionsOf (c : Cfg) (type : Expr) : MetaM (List Name) := do
  forallTelescope type fun xs _ => do
    let mut out := []
    for x in xs do
      for k in (← inferType x).getUsedConstants do
        if c.assume.contains k && !out.contains k then out := out ++ [k]
    return out

def auxTerms (env : Environment) (aux : NameSet) : String :=
  "".intercalate <| (names aux).toList.map fun n =>
    match env.find? n with
    | some ci => s!"\n#aux {n} {serialise ci.type} {((valueOf ci).map serialise).getD ""}"
    | none => ""

def report (c : Cfg) (n : Name) : MetaM (Json × NameSet) := do
  let env ← getEnv
  let some ci := env.find? n | throwError "declaration {n} not found"
  let axs ← collectAxioms n
  let line ← do
    let r ← findDeclarationRanges? n
    pure (r.map (·.range.pos.line) |>.getD 0)
  let isThm := ci matches .thmInfo _
  let tyC := ci.type.getUsedConstants
  let valC := ((valueOf ci).map (·.getUsedConstants)).getD #[]
  let (stmt, sAux) := resolve c env (if isThm then tyC else tyC ++ valC)
  let (proof, pAux) := if isThm then resolve c env valC else ({}, {})
  let proof := names proof |>.filter (!stmt.contains ·)
  let mut fields : List (String × Json) := [
    ("kind", kindOf ci),
    ("module", toString ((env.getModuleIdxFor? n).map (env.header.moduleNames[·]!) |>.getD `none)),
    ("line", line),
    ("axioms", toJson (axs.map toString |>.qsort (· < ·))),
    ("sorry", axs.contains `sorryAx),
    ("assumptions", toJson ((← assumptionsOf c ci.type).map toString)),
    ("type", ← ppStr ci.type),
    ("type_term", serialise ci.type),
    ("stmt_deps", toJson ((names stmt).map toString)),
    ("proof_deps", toJson (proof.map toString))]
  match valueOf ci with
  | some v =>
    if isThm then fields := fields ++ [("proof_term", Json.str (serialise v ++ auxTerms env (sAux.union pAux)))]
    else fields := fields ++ [("value", Json.str (← ppStr v)),
                              ("value_term", Json.str (serialise v ++ auxTerms env sAux))]
  | none => pure ()
  let nexts := (names stmt).toList ++ proof.toList
  return (Json.mkObj fields, NameSet.empty.insertMany nexts)

unsafe def main (args : List String) : IO UInt32 := do
  let kv (k : String) := args.findSome? fun a => if a.startsWith (k ++ "=") then some (a.drop (k.length + 1)).toString else none
  let some modName := kv "module" | IO.eprintln "need module=<Module>"; return 2
  let cfg : Cfg := { root := (kv "root").getD modName |>.toName,
                     assume := ((kv "assume").getD "").splitOn "," |>.filter (· ≠ "") |>.map String.toName }
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := modName.toName }] {} (loadExts := true)
  let stdin ← IO.getStdin
  let mut todo : List Name := []
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    let t := l.trimAscii.toString
    if t.endsWith "*" then  -- prefix: every project theorem whose name starts with it
      let pre := (t.dropEnd 1).toString
      for n in env.constants.fold (init := #[]) (fun acc n ci =>
          if isProject cfg n && ci matches .thmInfo _ && n.toString.startsWith pre then acc.push n else acc) do
        todo := n :: todo
    else if t != "" then todo := t.toName :: todo
  let mut done : NameSet := {}
  let mut out : List (String × Json) := []
  let ctx : Core.Context := { fileName := "<dump>", fileMap := default, options := maxRecDepth.set {} 4096 }
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if done.contains n then continue
      done := done.insert n
      let (j, nexts) ← try ((report cfg n).run' {} {}).toIO' ctx { env }
        catch e => throw (IO.userError s!"{n}: {e.toString}")
      out := out ++ [(n.toString, j)]
      todo := nexts.toList ++ todo
  IO.println (Json.mkObj [("toolchain", Json.str Lean.versionString), ("decls", Json.mkObj out)]).compress
  return 0
