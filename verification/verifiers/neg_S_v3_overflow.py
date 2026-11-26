# Overflow test of the positivity routine psd_kesin of the S verifier: X = [[-1]] is negative definite, so every
# call must be rejected, also for huge t where X - tI could wrap around in int64.
# The original test was run against the first version of the S verifier (which rejected all six cases as well);
# in this package it loads the final version verifiers/verify_S_v3.py. Run from the package root.
import sys, numpy as np
sys.argv=[sys.argv[0]]
sys.path.insert(0,'verifiers')
import importlib.util
spec=importlib.util.spec_from_file_location("dg",'verifiers/verify_S_v3.py')
dg=importlib.util.module_from_spec(spec); spec.loader.exec_module(dg)
X=np.array([[-1]],dtype=np.int64)          # explicitly NEGATIVE definite
for t in [1, 2**40, 2**62, 2**63-1, 2**63+5, 2**64-3]:
    try:
        alt=dg.psd_kesin(X,t,0,f"X=[[-1]], t={t}")
        print("   >>> RETURNED: λ_min ≥",float(alt), " (the true λ_min of X is -1)")
    except SystemExit as e:
        print("   (rejected via dur)")
    except Exception as e:
        print("   exception:",type(e).__name__,e)
