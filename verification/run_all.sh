#!/usr/bin/env bash
# run_all.sh -- re-run every computation of the package; outputs go to out/ (one text file per run).
#
#   ./run_all.sh            full run (about 10-15 min on the reference laptop; single runs need up to about 5 GB of memory)
#   ./run_all.sh --quick    skips the heavy runs (n = 10, 12 certificates, b = 12, 13 witnesses, the numerical remark)
#
# Afterwards:  python3 compare.py      (compares out/ with expected/)
#
# Requirements: `python3` on the PATH is Python 3.12 with NumPy 1.26.4 (see README.md). Every run is single-threaded
# (BLAS thread variables below) and niced. At most two heavy runs are executed at the same time (two lanes).
# Each run gets a time limit of RUN_TIMEOUT seconds (default 1800; RUN_TIMEOUT=0 disables it) if a `timeout`
# command is available. A run killed by the limit is recorded with exit status 124.
# The exit status of every run is recorded in out/run_log.tsv; several negative checks are EXPECTED to exit with 1.

set -u
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
QUICK=0
[ "${1:-}" = "--quick" ] && QUICK=1

OUT=out
rm -rf "$OUT"
mkdir -p "$OUT/time"
LOG="$OUT/run_log.tsv"
printf "name\texit_code\twall_seconds\n" > "$LOG"

RUN_TIMEOUT="${RUN_TIMEOUT:-1800}"
TO=""
if [ "$RUN_TIMEOUT" != "0" ]; then
  if command -v timeout >/dev/null 2>&1; then TO="timeout $RUN_TIMEOUT"; elif command -v gtimeout >/dev/null 2>&1; then TO="gtimeout $RUN_TIMEOUT"; fi
fi
TIMECMD=""
if /usr/bin/time -l true >/dev/null 2>&1; then TIMECMD="/usr/bin/time -l"; elif /usr/bin/time -v true >/dev/null 2>&1; then TIMECMD="/usr/bin/time -v"; fi

# run NAME command...   -> stdout+stderr of the command in out/NAME.txt, resource usage in out/time/NAME.time
run() {
  local name="$1"; shift
  local t0=$SECONDS
  if [ -n "$TIMECMD" ]; then
    $TO nice -n 15 $TIMECMD -o "$OUT/time/$name.time" "$@" > "$OUT/$name.txt" 2>&1
  else
    $TO nice -n 15 "$@" > "$OUT/$name.txt" 2>&1
  fi
  local rc=$?
  printf "%s\t%s\t%s\n" "$name" "$rc" "$((SECONDS - t0))" >> "$LOG"
  echo "[$(date '+%H:%M:%S')] $name: exit $rc, $((SECONDS - t0)) s"
}

PY=python3
echo "python: $($PY -c 'import sys, numpy; print(sys.version.split()[0], "numpy", numpy.__version__)')"
$PY -c 'import sys, platform, numpy; print("python", sys.version.split()[0]); print("numpy", numpy.__version__); print("platform", platform.platform())' > "$OUT/environment.txt" 2>&1

# ---------------------------------------------------------------- light runs (sequential)
# S certificates, final verifier v3 (int64 mode) and the second verifier (n <= 8)
for c in S_n4_K2_t1001 S_n6_K3_t1001 S_n8_K3_t1001 S_n8_K3_t1002 S_n8_K3_t1003; do
  run "S_v3_${c#S_}" $PY verifiers/verify_S_v3.py "certificates/S/$c.json"
done
for c in S_n4_K2_t1001 S_n6_K3_t1001 S_n8_K3_t1001 S_n8_K3_t1002 S_n8_K3_t1003; do
  run "S2_${c#S_}" $PY verifiers/verify_S2.py "certificates/S/$c.json"
done
# C certificates (two verifiers) and R certificates (n <= 8)
for c in C_n4_K2_Kp2_t1001 C_n6_K3_Kp2_t1001 C_n8_K3_Kp2_t1001 C_n8_K3_Kp2_t1002 C_n8_K3_Kp2_t1003; do
  run "C1_${c#C_}" $PY verifiers/verify_C1.py "certificates/C/$c.json"
  run "C2_${c#C_}" $PY verifiers/verify_C2.py "certificates/C/$c.json"
done
run R_n4_K2_j2_t1001 $PY verifiers/verify_R.py certificates/S/S_n4_K2_t1001.json 2
run R_n6_K3_j2_t1001 $PY verifiers/verify_R.py certificates/S/S_n6_K3_t1001.json 2
for s in 1001 1002 1003; do
  run "R_n8_K3_j3_t$s" $PY verifiers/verify_R.py "certificates/S/S_n8_K3_t$s.json" 3
done
# negative checks (several of these runs exit with 1 by design; see CLAIMS.md)
run neg_S_v3_corrupted       $PY verifiers/neg_S_v3.py certificates/S/S_n8_K3_t1001.json
run neg_S_v3_overflow_sweep  $PY verifiers/neg_S_v3_overflow.py
run neg_S_v3_counterexample  $PY verifiers/verify_S_v3.py certificates/negative/S_overflow_p.json
run neg_S_v3_blas_precondition $PY verifiers/verify_S_v3.py certificates/S/S_n8_K3_t1001.json --blas
run neg_C_corrupted          $PY verifiers/neg_C.py
run neg_S2_R_corrupted       $PY verifiers/neg_S2_R.py
# F_p witnesses (generic C(b,c)), b = 2..11, the C(8,2) witness and its independent check
run fp_hakem_c82             $PY witnesses/fp_witness.py hakem
run fp_c82_independent       $PY witnesses/c82_independent.py
for bc in "2 1" "3 1" "4 2" "5 2" "6 2" "7 2" "8 2" "9 3"; do
  set -- $bc
  run "fp_rastgele_b$1_c$2" $PY witnesses/fp_witness.py rastgele "$1" "$2" 1
done
run fp_rastgele_b4_c1_insufficient  $PY witnesses/fp_witness.py rastgele 4 1 1
for b in 10 11 12; do
  run "fp_rastgele_b${b}_c2_insufficient" $PY witnesses/fp_witness.py rastgele "$b" 2 1
done
run fp_simetrik_b10_c3       $PY witnesses/fp_witness.py simetrik 10 3 1
run fp_simetrik_b11_c3       $PY witnesses/fp_witness.py simetrik 11 3 1
run fp_b13_vector            $PY witnesses/b13_vector.py
run fp_witness_selftest      $PY witnesses/fp_witness_selftest.py
# Theorem 1 thresholds and constants, Proposition n >= 83, dynamic programming
run thm1_constants           $PY thresholds/thm1_constants.py
run n0_exact_a_100_700       $PY thresholds/n0_exact.py a 100 700
run n0_exact_a_700_1660      $PY thresholds/n0_exact.py a 700 1660
run n0_exact_b_1640_3200     $PY thresholds/n0_exact.py b 1640 3200
run n0_exact_b_3200_5100     $PY thresholds/n0_exact.py b 3200 5100
run n0_exact_c_200_5000      $PY thresholds/n0_exact.py c 200 5000
run n0_log_margin            $PY thresholds/n0_log_margin.py
run thm1_examples_exact      $PY thresholds/examples_exact.py
run prop_half83              $PY thresholds/prop_half83.py
run lemma23_partA            $PY thresholds/lemma23.py A
run lagrangian_cover         $PY thresholds/lagrangian_cover.py
run dp_glue_b2-13            $PY thresholds/dp_glue.py 2,3,4,5,6,7,8,9,10,11,12,13
run dp_no_S                  $PY thresholds/dp_no_S.py
run dp_qubit_chain           $PY thresholds/dp_qubit_chain.py

if [ "$QUICK" = 1 ]; then
  echo "--quick: heavy runs skipped"
  exit 0
fi

# ---------------------------------------------------------------- heavy runs: two lanes in parallel
laneA() {
  run S_v3_n10_K4_t1001        $PY verifiers/verify_S_v3.py certificates/S/S_n10_K4_t1001.json
  run C1_n10_K4_Kp3_t1001      $PY verifiers/verify_C1.py certificates/C/C_n10_K4_Kp3_t1001.json
  run C2_n10_K4_Kp3_t1001      $PY verifiers/verify_C2.py certificates/C/C_n10_K4_Kp3_t1001.json
  run R_n10_K4_j3_t1001        $PY verifiers/verify_R.py certificates/S/S_n10_K4_t1001.json 3
}
laneB() {
  run S_v3_n12_K4_t1001_blas   $PY verifiers/verify_S_v3.py certificates/S/S_n12_K4_t1001.json --blas
  run fp_simetrik_b12_c3       $PY witnesses/fp_witness.py simetrik 12 3 1
  run fp_sektor_b13_c3_cift    $PY witnesses/fp_witness.py sektor 13 3 1 cift
  run fp_sektor_b13_c3_tek     $PY witnesses/fp_witness.py sektor 13 3 1 tek
  run numerics_glue_8x4_K3_K4  $PY numerics/direct_glue_rank.py S_n8_K3_t1001.json S_n4_K2_t1001.json 3,4 gram
}
laneA &
PA=$!
laneB &
PB=$!
wait $PA $PB
echo "done; now run: python3 compare.py"
