"""Discharge every hidden certificate with Z3 and refresh RESULTS*.md.

Two logics run here:

* `ga_proofs` -- the frozen tables (`RESULTS.md`);
* `cat_proofs` -- the categorified layer built on top of them
  (`RESULTS_CAT.md`): Koszul cohomology, the Loewy filtration and the
  Cohen--Maclane graded ring.

Both read the tables that ship inside the MoonBit packages.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ga_proofs as G
import cat_proofs as C

HERE = os.path.dirname(os.path.abspath(__file__))

G.run()
C.run()
ok = G.report(os.path.join(HERE, "RESULTS.md"))
ok = C.report(os.path.join(HERE, "RESULTS_CAT.md")) and ok
print("all certificates: %s" % ("PASS" if ok else "FAIL"))
sys.exit(0 if ok else 1)