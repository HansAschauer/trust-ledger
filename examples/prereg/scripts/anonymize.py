"""Public data set from the private responses: drop pseudonyms and free text, age in bands of ten years."""
import csv

rows = list(csv.DictReader(open("private/responses.csv")))
with open("data/responses-anon.csv", "w", newline="") as f:
    w = csv.writer(f, lineterminator="\n")
    w.writerow(["age_band", "condition", "attention_ok", "score"])
    for r in sorted(rows, key=lambda r: (r["condition"], r["score"], r["age"])):  # no order that could re-identify
        band = int(r["age"]) // 10 * 10
        w.writerow([f"{band}-{band + 9}", r["condition"], r["attention_ok"], r["score"]])
