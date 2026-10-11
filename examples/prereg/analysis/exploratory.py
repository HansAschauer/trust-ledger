"""Exploratory (not preregistered): mean score by age band, both conditions together."""
import csv, json

rows = [r for r in csv.DictReader(open("data/responses-anon.csv")) if r["attention_ok"] == "yes"]
bands = sorted({r["age_band"] for r in rows})
json.dump({b: round(sum(float(r["score"]) for r in rows if r["age_band"] == b) /
                    len([r for r in rows if r["age_band"] == b]), 2) for b in bands},
          open("results/age.json", "w"), indent=1)
