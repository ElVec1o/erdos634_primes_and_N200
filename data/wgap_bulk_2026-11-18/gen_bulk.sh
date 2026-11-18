#!/bin/bash
# NOTE (release 6.0): archived build script of the internal run; it refers to the project's internal directory layout and does not run in this repository. Kept for the record (commands, parameters).
# gen_bulk.sh <BLK> <G> <N> [N ...]     (bash/awk only; extends gen_chunk4.sh + gen_final.sh)
# Writes, under lean/Erdos634/Draft/ (never overwrites an existing file):
#   WGapB<BLK>c<k>.lean  chain module k: for each of up to G values N of the block, the 14 non-S2 conjuncts (decide +kernel each),
#                        the pruned S2 pieces (RangeAll ... (S2B N A)), and the assembler  b_cp2c_<N> : CNzFixP2 N  (one module per group).
#                        Values N >= SPLITAT (default 500000) put the heavy half of the conjuncts in a second module  WGapB<BLK>q<k>
#                        (lemmas b_lq_<N>_*), imported by the chain module.
#   WGapB<BLK>F.lean     HEAVY batch: imports WGapLightLink2 + the chain modules; b_final_<N> : not TileCount N for every N of the block.
#   WGapB<BLK>X.lean     block axioms module: #print axioms for every b_final_<N>.
# and  internal working notes>.mods  (chain modules in build order, then F, then X) and <BLK>.nlist.
# Credits (also written into each module docstring): Beeson (theta targets, Lemma 52), Paliy, Beeson-Rosu, Laczkovich, Zhang, Herdt.
isq() { awk -v n=$1 'BEGIN{s=int(sqrt(n)); while(s*s>n)s--; while((s+1)*(s+1)<=n)s++; print s}'; }
ROOT=a scratch directory
D=$ROOT/lean/Erdos634/Draft
R=$ROOT/internal working notes
BLK=$1; G=$2; shift; shift
BUD=${BUD:-4000}; SPLITAT=${SPLITAT:-500000}
CRED="Credits: Beeson (theta targets, Lemma 52), Paliy, Beeson-Rosu, Laczkovich, Zhang, Herdt.  UNAUDITED beyond internal checks.  No sorry, no native_decide."
MODS=$R/blocks/$BLK.mods; : > $MODS; printf '%s\n' "$@" > $R/blocks/$BLK.nlist
HDR() { # $1 = extra import lines
  echo "import Erdos634.Draft.WGapLightChunk2"; [ -n "$1" ] && echo "$1"
  echo "set_option maxRecDepth 8000"; echo "set_option synthInstance.maxSize 20000"; echo "set_option synthInstance.maxHeartbeats 2000000"
  echo "namespace Erdos634.Draft.WGapPure"
}
# emit_rest <N> <out-main-fd-is-stdout> : conjunct theorems; heavy half to fd 3 when split
emit_N() { # $1 = N, $2 = 1 if split (fd 3 open for the q module)
  local N=$1 SPLIT=$2 M4 SQ d A DIVS PIECES SEEN SEEN2 qa qb lo hi len p rest disj
  M4=$((4*N)); SQ=$(isq $M4)
  if [ $SPLIT -eq 1 ]; then Q=3; else Q=1; fi
  echo "theorem b_lf1_$N : NQChkW $N := by decide +kernel"
  echo "theorem b_lf2_$N : Cell2 $N := by decide +kernel"
  echo "theorem b_lf3_$N : NSqChkSq $N := by decide +kernel"
  echo "theorem b_lf4_$N : HArithChkSq $N := by decide +kernel"
  echo "theorem b_lf5_$N : ($N % 2 = 1 ∨ ($N % 2 = 0 ∧ NHSqChkSq $N)) := by decide +kernel"
  if [ $((N % 4)) -eq 2 ]; then
    echo "theorem b_lf6_$N : LeafEsqSR $N := Or.inl (by norm_num)"
  else
    echo "theorem b_lf6a_$N : Pairs60R $N := by decide +kernel"
    echo "theorem b_lf6b_$N : Pairs120R $N := by decide +kernel"
    echo "theorem b_lf6_$N : LeafEsqSR $N := Or.inr ⟨by norm_num, b_lf6a_$N, b_lf6b_$N⟩"
  fi
  echo "theorem b_lf7_$N : ($N % 4 = 2 ∨ F1ChkParW $N) := by decide +kernel"
  echo "theorem b_lf11a_$N : NoF2S $N := by decide +kernel"
  echo "theorem b_lf11b_$N : NoF3zS $N := by decide +kernel"
  echo "theorem b_lf11c_$N : NoF4zS $N := by decide +kernel"
  {
  echo "theorem b_lf9_$N : S3newChk $N := by decide +kernel"
  echo "theorem b_lf10_$N : IsoH9bChkW $N := by decide +kernel"
  echo "theorem b_lf12_$N : GammaChkDW $N := by decide +kernel"
  echo "theorem b_lf13_$N : S1UBChkW $N := by decide +kernel"
  echo "theorem b_lf14_$N : RWChkWl $N := by decide +kernel"
  echo "theorem b_lf15_$N : S5wChkW $N := by decide +kernel"
  } >&$Q
  DIVS=""; d=1
  while [ $d -le $SQ ]; do [ $((M4 % d)) -eq 0 ] && DIVS="$DIVS $d"; d=$((d+1)); done
  PIECES=""; SEEN2=""
  for d in $DIVS; do for A in $d $((M4/d)); do
    case " $SEEN2 " in *" $A "*) continue;; esac
    SEEN2="$SEEN2 $A"
    qa=$(( $(isq $((A/2))) + 1 )); qb=$(( $(isq $((A-1))) + 1 )); [ $qb -gt $((SQ+1)) ] && qb=$((SQ+1)); [ $qa -gt $qb ] && qa=$qb
    lo=$qa
    while [ $lo -lt $qb ]; do hi=$((lo+BUD)); [ $hi -gt $qb ] && hi=$qb; PIECES="$PIECES $A:$lo:$hi"; lo=$hi; done
  done; done
  for p in $PIECES; do
    A=${p%%:*}; rest=${p#*:}; lo=${rest%%:*}; hi=${rest#*:}
    echo "theorem b_sp_${N}_${A}_${lo} : RangeAll $lo $hi (S2B $N $A) := by decide +kernel"
  done
  echo "theorem b_hB_$N : Nat.sqrt (4 * $N) = $SQ := by decide +kernel"
  SEEN=""
  for d in $DIVS; do for A in $d $((M4/d)); do
    case " $SEEN " in *" $A "*) continue;; esac
    SEEN="$SEEN $A"
    qa=$(( $(isq $((A/2))) + 1 )); qb=$(( $(isq $((A-1))) + 1 )); [ $qb -gt $((SQ+1)) ] && qb=$((SQ+1)); [ $qa -gt $qb ] && qa=$qb
    local expr="(s2B_vac_low (N := $N) (A := $A) (hi := $qa) (by norm_num))"
    lo=$qa
    while [ $lo -lt $qb ]; do
      hi=$((lo+BUD)); [ $hi -gt $qb ] && hi=$qb
      expr="(rangeAll_append $expr b_sp_${N}_${A}_${lo} (by omega) (by omega))"
      lo=$hi
    done
    if [ $qb -le $SQ ]; then expr="(rangeAll_append $expr (s2B_vac_high (N := $N) (A := $A) (lo := $qb) (hi := $((SQ+1))) (by norm_num)) (by omega) (by omega))"; fi
    echo "theorem b_hA_${N}_${A} : S2Q $N $A := s2Q_of_B (by rw [b_hB_$N]; exact forall_le_of_rangeAll (B := $SQ) (p := S2B $N $A) $expr)"
  done; done
  disj=""
  for d in $DIVS; do if [ -z "$disj" ]; then disj="d = $d"; else disj="$disj ∨ d = $d"; fi; done
  echo "theorem b_hmem_$N : ∀ d ≤ Nat.sqrt (4 * $N), 0 < d → d ∣ 4 * $N → $disj := by decide +kernel"
  echo "theorem b_s2d_$N : S2D $N := by"
  echo "  intro d hd h0 hdv"
  echo "  rcases b_hmem_$N d hd h0 hdv with h | $(echo $DIVS | awk '{s=""; for(i=2;i<=NF;i++){s=s (i>2?" | ":"") "h"} print s}')"
  for d in $DIVS; do
    echo "  · subst_vars"
    echo "    refine ⟨b_hA_${N}_${d}, ?_⟩"
    echo "    have e : 4 * $N / $d = $((M4/d)) := by norm_num"
    echo "    rw [e]; exact b_hA_${N}_$((M4/d))"
  done
  echo "theorem b_cp2c_$N : CNzFixP2 $N :="
  echo "  ⟨b_lf1_$N, b_lf2_$N, b_lf3_$N, b_lf4_$N, b_lf5_$N, b_lf6_$N, b_lf7_$N, b_s2d_$N, b_lf9_$N, b_lf10_$N, ⟨b_lf11a_$N, b_lf11b_$N, b_lf11c_$N⟩, b_lf12_$N, b_lf13_$N, b_lf14_$N, b_lf15_$N⟩"
}
k=0; CH=""; ALLN=""
while [ $# -gt 0 ]; do
  grp=""; i=0
  while [ $i -lt $G ] && [ $# -gt 0 ]; do grp="$grp $1"; shift; i=$((i+1)); done
  F=$D/WGapB${BLK}c$k.lean
  [ -e $F ] && { echo "refusing: $F exists"; exit 1; }
  # does the group contain a split value? then every value of the group is split (fd 3 -> q module)
  SPL=0; for N in $grp; do [ $N -ge $SPLITAT ] && SPL=1; done
  if [ $SPL -eq 1 ]; then
    Qf=$D/WGapB${BLK}q$k.lean; [ -e $Qf ] && { echo "refusing: $Qf exists"; exit 1; }
    { echo "/- WGapB${BLK}q$k: heavy half of the non-S2 conjuncts of CNzFixP2 N for N in:$grp.  Generated by gen_bulk.sh.  $CRED -/"; HDR ""; } > $Qf
    exec 3>>$Qf
    echo "Erdos634.Draft.WGapB${BLK}q$k" >> $MODS
  fi
  { echo "/- WGapB${BLK}c$k: CNzFixP2 N for N in:$grp (non-S2 conjuncts, pruned S2 pieces, assembler).  Generated by gen_bulk.sh.  $CRED -/"
    if [ $SPL -eq 1 ]; then HDR "import Erdos634.Draft.WGapB${BLK}q$k"; else HDR ""; fi
    for N in $grp; do emit_N $N $SPL; done
    echo "end Erdos634.Draft.WGapPure"; } > $F
  if [ $SPL -eq 1 ]; then echo "end Erdos634.Draft.WGapPure" >&3; exec 3>&-; fi
  echo "Erdos634.Draft.WGapB${BLK}c$k" >> $MODS
  echo "WGapB${BLK}c$k$grp" >> $R/blocks/$BLK.groups
  CH="$CH $k"; ALLN="$ALLN$grp"; k=$((k+1))
done
if [ "${NOFX:-0}" = 1 ]; then echo "block $BLK (chain only): $(echo $ALLN | wc -w) N, $k groups"; exit 0; fi
FB=$D/WGapB${BLK}F.lean; XB=$D/WGapB${BLK}X.lean
[ -e $FB ] && { echo "refusing: $FB exists"; exit 1; }
{ echo "/- WGapB${BLK}F: HEAVY batch of not-TileCount theorems (gen_bulk.sh).  $CRED -/"
  echo "import Erdos634.Draft.WGapLightLink2"
  for c in $CH; do echo "import Erdos634.Draft.WGapB${BLK}c$c"; done
  echo "namespace Erdos634.Draft.WGapPure"
  for N in $ALLN; do echo "theorem b_final_$N : ¬ Erdos634.Draft.TileCountFamilies.TileCount $N := not_tileCount_of_P $N (cnzFixP_of_P2 b_cp2c_$N)"; done
  echo "end Erdos634.Draft.WGapPure"; } > $FB
{ echo "/- WGapB${BLK}X: axioms of every final theorem of block ${BLK} (gen_bulk.sh).  $CRED -/"
  echo "import Erdos634.Draft.WGapB${BLK}F"
  for N in $ALLN; do echo "#print axioms Erdos634.Draft.WGapPure.b_final_$N"; done; } > $XB
echo "Erdos634.Draft.WGapB${BLK}F" >> $MODS; echo "Erdos634.Draft.WGapB${BLK}X" >> $MODS
echo "block $BLK: $(echo $ALLN | wc -w) N, $k chain groups, mods listed in $MODS"
