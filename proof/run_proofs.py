"""Discharge every hidden certificate with Z3 and refresh RESULTS.md."""
import sys
import ga_proofs as G

G.run()
ok = G.report(__file__.replace("run_proofs.py", "RESULTS.md"))
sys.exit(0 if ok else 1)
