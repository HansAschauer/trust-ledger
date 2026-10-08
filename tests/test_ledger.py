import json, shutil, sys, tempfile, unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
import ledger as lg

TOY = ROOT / "examples" / "toy"


class Toy(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        shutil.copytree(TOY, self.tmp / "p")
        self.p = self.tmp / "p"

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def edit_dump(self, fn):
        f = self.p / "ledger" / "lean.json"
        d = json.loads(f.read_text()); fn(d["decls"]); f.write_text(json.dumps(d))

    def L(self):
        return lg.Ledger(self.p)

    def attest(self, claim="thm-twice"):
        lg.main(["-C", str(self.p), "attest", claim, "--person", "X", "--level", "green"])

    def test_deterministic(self):
        self.assertEqual(self.L().root_hash, self.L().root_hash)

    def test_proof_change_keeps_attestation_but_changes_root(self):
        self.attest()
        r0 = self.L().root_hash
        self.edit_dump(lambda d: d["Toy.lem"].update(proof="fun n => by omega"))
        L = self.L()
        self.assertNotEqual(L.root_hash, r0)                    # evidence changed
        self.assertTrue(all(cur for *_, cur in L.attestation_state("thm-twice")))  # statement did not

    def test_statement_change_resets_attestations_up_the_uses_chain(self):
        self.attest("lem-succ"); self.attest("thm-twice")
        self.edit_dump(lambda d: d["Toy.f"].update(value="fun n => n + 2"))  # a definition changes
        L = self.L()
        self.assertFalse(L.attestation_state("lem-succ")[0][3])
        self.assertFalse(L.attestation_state("thm-twice")[0][3])

    def test_uses_dependency_resets_dependent_claim(self):
        self.attest("thm-twice")
        self.edit_dump(lambda d: d["Toy.lem"].update(type="∀ n, Toy.f n ≥ n"))
        # thm-twice lists lem-succ in `uses`, whose statement changed
        self.assertFalse(self.L().attestation_state("thm-twice")[0][3])

    def test_verify_detects_tampering(self):
        lg.main(["-C", str(self.p), "lock"])
        self.assertEqual(lg.main(["-C", str(self.p), "verify"]), 0)
        self.edit_dump(lambda d: d["Toy.lem"].update(sorry=True))
        self.assertEqual(lg.main(["-C", str(self.p), "verify"]), 1)

    def test_register_propagates(self):
        r = self.L().register
        self.assertIn("hyp:cited:banach", r["conj-general"])
        self.assertIn("assertion:conj-general-hint", r["conj-general"])
        self.assertEqual(r["lem-succ"], [])

    def test_unattested_claim_changes_nothing_about_others(self):
        L0 = self.L()
        self.edit_dump(lambda d: d["Toy.thm"].update(proof="x"))
        L1 = self.L()
        self.assertEqual(L0.full["claim:lem-succ"], L1.full["claim:lem-succ"])
        self.assertNotEqual(L0.full["claim:thm-twice"], L1.full["claim:thm-twice"])


class Latex(Toy):
    def tex(self, rel, fn):
        f = self.p / "paper" / rel
        f.write_text(fn(f.read_text()))

    def L(self):  # these tests work on the toy paper only
        return lg.Ledger(self.p, "toy")

    def test_statement_extracted_from_tex(self):
        L = self.L()
        text, src = L.stmt["lem-succ"]
        self.assertEqual(src, "tex")
        self.assertEqual(text, "[lem:succ] lemma: For every $n$, $f(n) > n$.")  # comment and label removed

    def test_theorem_edit_in_paper_resets_attestation(self):
        self.attest("lem-succ")
        self.tex("chapters/results.tex", lambda t: t.replace("f(n) > n", "f(n) \\ge n"))
        self.assertFalse(self.L().attestation_state("lem-succ")[0][3])

    def test_comment_edit_keeps_attestation_but_changes_root(self):
        self.attest("lem-succ")
        r0 = self.L().root_hash
        self.tex("chapters/results.tex", lambda t: t.replace("not part of the statement", "still not"))
        L = self.L()
        self.assertTrue(L.attestation_state("lem-succ")[0][3])  # the statement text is unchanged
        self.assertNotEqual(L.root_hash, r0)                     # but the source file is different

    def test_prose_edit_changes_root_only(self):
        self.attest("lem-succ")
        r0 = self.L().root_hash
        self.tex("main.tex", lambda t: t.replace("Some prose", "Some other prose"))
        L = self.L()
        self.assertNotEqual(L.root_hash, r0)
        self.assertTrue(L.attestation_state("lem-succ")[0][3])

    def test_generated_directory_excluded(self):
        r0 = self.L().root_hash
        (self.p / "paper" / "ledger" / "toy-root.tex").write_text("changed")
        self.assertEqual(self.L().root_hash, r0)

    def test_scope_excludes_other_paper_and_is_independent_of_it(self):
        full = lg.Ledger(self.p)
        self.assertIn("other-paper", full.claims)
        L = self.L()
        self.assertNotIn("other-paper", L.claims)
        f = self.p / "ledger" / "claims.toml"
        f.write_text(f.read_text().replace("Belongs to another paper.", "Changed."))
        self.assertEqual(self.L().root_hash, L.root_hash)
        self.assertNotEqual(lg.Ledger(self.p).root_hash, full.root_hash)

    def test_missing_label_is_an_error(self):
        self.tex("chapters/results.tex", lambda t: t.replace("\\label{lem:succ}", ""))
        self.assertTrue(any("lem:succ" in e for e in self.L().errors))

    def test_lock_per_paper(self):
        self.assertEqual(lg.main(["-C", str(self.p), "-P", "toy", "lock"]), 0)
        self.assertTrue((self.p / "ledger" / "lock-toy.json").exists())
        self.assertEqual(lg.main(["-C", str(self.p), "-P", "toy", "verify"]), 0)

    def test_nested_input_resolved_relative_to_main(self):
        (self.p / "paper" / "chapters" / "more.tex").write_text("Nested.\n")
        self.tex("chapters/results.tex", lambda t: t + "\\input{chapters/more}\n")  # not chapters/chapters/more
        L = self.L()
        self.assertIn("paper/chapters/more.tex", L.paper_nodes["toy"]["files"])
        self.assertEqual(L.unresolved["toy"], [])

    def test_strip_comments(self):
        self.assertEqual(lg.strip_comments("a % c\nb \\% d\nc \\\\% e"), "a \nb \\% d\nc \\\\")


class Merkle(unittest.TestCase):
    def test_cycle_members_share_dependence(self):
        pay = {"a": 1, "b": 2, "c": 3}
        h1 = lg.merkle(pay, {"a": ["b"], "b": ["a"], "c": ["a"]}, "t")
        h2 = lg.merkle({**pay, "b": 99}, {"a": ["b"], "b": ["a"], "c": ["a"]}, "t")
        self.assertNotEqual(h1["a"], h2["a"]); self.assertNotEqual(h1["c"], h2["c"])

    def test_order_independent(self):
        h1 = lg.merkle({"a": 1, "b": 2}, {"a": ["b", "b"]}, "t")
        h2 = lg.merkle({"b": 2, "a": 1}, {"a": ["b"]}, "t")
        self.assertEqual(h1, h2)

    def test_floats_rejected(self):
        with self.assertRaises(ValueError):
            lg.canon({"x": 1.5})


if __name__ == "__main__":
    unittest.main()
