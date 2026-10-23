import Submission.Work.TensorProto.Strictify
import Submission.Work.BlockAccounting.Moment4
import Submission.Work.BlockAccounting.Sharp

set_option maxRecDepth 8000

namespace TensorProto
open OAI.PowerSaving.BlockAccounting

noncomputable section

namespace Cascade8

@[irreducible] def ofHist (l : List (ℕ × ℕ)) : Multiset ℕ := (l.map fun b => Multiset.replicate b.2 b.1).sum

def TPCascade8 : List (ℕ × ℕ) := [(4, 504), (7, 126), (8, 846), (9, 5868), (17, 1792), (25, 1792)]
def PPCascade8 : List (ℕ × ℕ) := [(1, 41946), (2, 6984), (3, 8892), (4, 2646), (5, 648), (8, 144)]

lemma mom_ofHist (t : ℝ) (l : List (ℕ × ℕ)) :
    mom t (ofHist l) = (l.map fun b => (b.2 : ℝ) * ((b.1 : ℝ) ^ t)).sum := by
  induction l with
  | nil => simp [ofHist]
  | cons b l ih =>
    have e : ofHist (b :: l) = Multiset.replicate b.2 b.1 + ofHist l := by simp [ofHist]
    rw [e, mom_add, mom_replicate, ih, List.map_cons, List.sum_cons]

lemma mom_ofHist_moment (t : ℝ) (l : List (ℕ × ℕ)) {M : ℕ} (hM : 0 < M) :
    mom t (ofHist l) = (M : ℝ) ^ t * moment M t l := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hMt : 0 < (M : ℝ) ^ t := Real.rpow_pos_of_pos hM' t
  rw [mom_ofHist, moment, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro b _
  rw [Real.div_rpow (Nat.cast_nonneg _) hM'.le, mul_div_assoc', mul_div_assoc',
    mul_div_cancel_left₀ _ hMt.ne']

lemma card_ofHist (l : List (ℕ × ℕ)) : Multiset.card (ofHist l) = (l.map Prod.snd).sum := by
  induction l with
  | nil => simp [ofHist]
  | cons b l ih =>
    have e : ofHist (b :: l) = Multiset.replicate b.2 b.1 + ofHist l := by simp [ofHist]
    rw [e, Multiset.card_add, Multiset.card_replicate, ih, List.map_cons, List.sum_cons]

lemma mom_one_ofHist (l : List (ℕ × ℕ)) : mom 1 (ofHist l) = ((l.map fun b => b.2 * b.1).sum : ℕ) := by
  rw [mom_ofHist]
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, Real.rpow_one]
    push_cast
    ring

lemma b0 : T 25 (1 - ((4:ℝ)/25)) 1 41946 ≤ ((28088302638939:ℝ)/10000000000) :=
  term_le4 25 1 41946 ((4:ℝ)/25) ((10058987:ℝ)/3125000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_of_le_expsum _ _ 18 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num) (by norm_num)

lemma b1 : T 25 (1 - ((4:ℝ)/25)) 2 6984 ≤ ((4185260227611:ℝ)/5000000000) :=
  term_le4 25 2 6984 ((4:ℝ)/25) ((126286433:ℝ)/50000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_of_le_expsum _ _ 16 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num) (by norm_num)

lemma b2 : T 25 (1 - ((4:ℝ)/25)) 3 8892 ≤ ((7490522512173:ℝ)/5000000000) :=
  term_le4 25 3 8892 ((4:ℝ)/25) ((42405271:ℝ)/20000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_of_le_expsum _ _ 15 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num) (by norm_num)

lemma b3 : T 25 (1 - ((4:ℝ)/25)) 4 2646 ≤ ((5676353293211:ℝ)/10000000000) :=
  term_le4 25 4 2646 ((4:ℝ)/25) ((45814537:ℝ)/25000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_of_le_expsum _ _ 14 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num) (by norm_num)

lemma b4 : T 25 (1 - ((4:ℝ)/25)) 5 648 ≤ ((419172014273:ℝ)/2500000000) :=
  term_le4 25 5 648 ((4:ℝ)/25) ((160943793:ℝ)/100000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_of_le_expsum _ _ 14 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num) (by norm_num)

lemma b5 : T 25 (1 - ((4:ℝ)/25)) 8 144 ≤ ((22118313259:ℝ)/400000000) :=
  term_le4 25 8 144 ((4:ℝ)/25) ((11394343:ℝ)/10000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (log_le_of_le_expsum _ _ 12 (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num) (by norm_num)

lemma c0 : ((1080899702541:ℝ)/10000000000) ≤ T 25 (1 - ((4:ℝ)/25)) 4 504 :=
  term_ge 25 4 504 ((4:ℝ)/25) ((36651629:ℝ)/20000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_log_of_expbound _ _ 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num)

lemma c1 : ((21623541351:ℝ)/500000000) ≤ T 25 (1 - ((4:ℝ)/25)) 7 126 :=
  term_ge 25 7 126 ((4:ℝ)/25) ((63648283:ℝ)/50000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_log_of_expbound _ _ 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num)

lemma c2 : ((3248471484237:ℝ)/10000000000) ≤ T 25 (1 - ((4:ℝ)/25)) 8 846 :=
  term_ge 25 8 846 ((4:ℝ)/25) ((113943427:ℝ)/100000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_log_of_expbound _ _ 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num)

lemma c3 : ((24875559868693:ℝ)/10000000000) ≤ T 25 (1 - ((4:ℝ)/25)) 9 5868 :=
  term_ge 25 9 5868 ((4:ℝ)/25) ((102165123:ℝ)/100000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_log_of_expbound _ _ 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num)

lemma c4 : ((2592240175459:ℝ)/2000000000) ≤ T 25 (1 - ((4:ℝ)/25)) 17 1792 :=
  term_ge 25 17 1792 ((4:ℝ)/25) ((38566247:ℝ)/100000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_log_of_expbound _ _ 1 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
    (by norm_num)

lemma ctop : T 25 (1 - ((4:ℝ)/25)) 25 1792 = 1792 := by
  unfold T; rw [div_self (show ((25:ℕ):ℝ) ≠ 0 by norm_num), Real.one_rpow]; norm_num

lemma hsumP : moment 25 (1 - ((4:ℝ)/25)) PPCascade8 = (T 25 (1 - ((4:ℝ)/25)) 1 41946 + (T 25 (1 - ((4:ℝ)/25)) 2 6984 + (T 25 (1 - ((4:ℝ)/25)) 3 8892 + (T 25 (1 - ((4:ℝ)/25)) 4 2646 + (T 25 (1 - ((4:ℝ)/25)) 5 648 + (T 25 (1 - ((4:ℝ)/25)) 8 144 + (0))))))) := rfl

lemma hsumT : moment 25 (1 - ((4:ℝ)/25)) TPCascade8 = (T 25 (1 - ((4:ℝ)/25)) 4 504 + (T 25 (1 - ((4:ℝ)/25)) 7 126 + (T 25 (1 - ((4:ℝ)/25)) 8 846 + (T 25 (1 - ((4:ℝ)/25)) 9 5868 + (T 25 (1 - ((4:ℝ)/25)) 17 1792 + (T 25 (1 - ((4:ℝ)/25)) 25 1792 + (0))))))) := rfl

theorem paid_le : moment 25 (1 - ((4:ℝ)/25)) PPCascade8 ≤ ((11869173460057:ℝ)/2000000000) := by
  rw [hsumP]
  have := b0; have := b1; have := b2; have := b3; have := b4; have := b5
  linarith

theorem target_ge : ((30259301379893:ℝ)/5000000000) ≤ moment 25 (1 - ((4:ℝ)/25)) TPCascade8 := by
  rw [hsumT]
  have := c0; have := c1; have := c2; have := c3; have := c4; have := ctop
  linarith

theorem scale_le : ((25:ℝ)/4) ^ ((4:ℝ)/25) ≤ ((503507:ℝ)/500000) := by
  have hx : (0:ℝ) < 25/4 := by norm_num
  have hL : Real.log ((25:ℝ)/4) ≤ ((45814537:ℝ)/25000000) :=
    log_le_of_le_expsum _ _ 14 (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rw [Real.rpow_def_of_pos hx]
  have hC : (0:ℝ) ≤ ((4:ℝ)/25) := by norm_num
  have h1 : Real.exp (Real.log ((25:ℝ)/4) * ((4:ℝ)/25)) ≤ Real.exp (((4:ℝ)/25) * ((45814537:ℝ)/25000000)) := by
    apply Real.exp_le_exp.mpr
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hL hC
  have h2 := exp_le_quartic (((4:ℝ)/25) * ((45814537:ℝ)/25000000)) (by norm_num) (by norm_num)
  refine h1.trans (h2.trans ?_)
  norm_num

lemma T_pos : 0 < mom (1 - ((4:ℝ)/25)) (ofHist TPCascade8) := by
  rw [mom_ofHist_moment (1 - ((4:ℝ)/25)) TPCascade8 (M := 25) (by norm_num)]
  have h := target_ge
  have hm : (0:ℝ) < ((25:ℕ):ℝ) ^ (1 - ((4:ℝ)/25)) := Real.rpow_pos_of_pos (by norm_num) _
  have hM : 0 < moment 25 (1 - ((4:ℝ)/25)) TPCascade8 := lt_of_lt_of_le (by norm_num) h
  exact mul_pos hm hM

theorem alpha : mom (1 - ((4:ℝ)/25)) (ofHist PPCascade8) ≤ (1 - ((1:ℝ)/4294967296)) * mom (1 - ((4:ℝ)/25)) (ofHist TPCascade8) := by
  have eP := mom_ofHist_moment (1 - ((4:ℝ)/25)) PPCascade8 (M := 25) (by norm_num)
  have eT := mom_ofHist_moment (1 - ((4:ℝ)/25)) TPCascade8 (M := 25) (by norm_num)
  have hm : (0:ℝ) ≤ ((25:ℕ):ℝ) ^ (1 - ((4:ℝ)/25)) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hnum : ((11869173460057:ℝ)/2000000000) ≤ (1 - ((1:ℝ)/4294967296) : ℝ) * ((30259301379893:ℝ)/5000000000) := by norm_num
  have h3 : moment 25 (1 - ((4:ℝ)/25)) PPCascade8 ≤ (1 - ((1:ℝ)/4294967296)) * moment 25 (1 - ((4:ℝ)/25)) TPCascade8 :=
    paid_le.trans (hnum.trans (mul_le_mul_of_nonneg_left target_ge (by norm_num)))
  rw [eP, eT]
  exact (mul_le_mul_of_nonneg_left h3 hm).trans_eq (mul_left_comm _ _ _)

theorem scaled_target : (25:ℝ) * ((30259301379893:ℝ)/5000000000) / ((503507:ℝ)/500000) ≤ ((4:ℕ):ℝ) ^ ((4:ℝ)/25) * mom (1 - ((4:ℝ)/25)) (ofHist TPCascade8) := by
  rw [mom_ofHist_moment (1 - ((4:ℝ)/25)) TPCascade8 (M := 25) (by norm_num)]
  have h2 := target_ge
  have hE := scale_le
  have hpos : (0:ℝ) < ((25:ℝ)/4) ^ ((4:ℝ)/25) := Real.rpow_pos_of_pos (by norm_num) _
  have e : ((4:ℕ):ℝ) ^ ((4:ℝ)/25) * ((25:ℕ):ℝ) ^ (1 - ((4:ℝ)/25)) = 25 / ((25:ℝ)/4) ^ ((4:ℝ)/25) := by
    rw [Real.div_rpow (show (0:ℝ) ≤ 25 by norm_num) (show (0:ℝ) ≤ 4 by norm_num),
      Real.rpow_sub (show (0:ℝ) < ((25:ℕ):ℝ) by norm_num), Real.rpow_one]
    push_cast
    rw [div_div_eq_mul_div, mul_div_assoc']
    ring
  calc (25:ℝ) * ((30259301379893:ℝ)/5000000000) / ((503507:ℝ)/500000)
      ≤ 25 * moment 25 (1 - ((4:ℝ)/25)) TPCascade8 / ((25:ℝ)/4) ^ ((4:ℝ)/25) := by
        rw [div_le_div_iff₀ (by norm_num) hpos]
        have h4 : (25:ℝ) * ((30259301379893:ℝ)/5000000000) ≤ 25 * moment 25 (1 - ((4:ℝ)/25)) TPCascade8 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
        exact mul_le_mul h4 hE hpos.le (mul_nonneg (by norm_num) (le_trans (by norm_num) h2))
    _ = ((4:ℕ):ℝ) ^ ((4:ℝ)/25) * (((25:ℕ):ℝ) ^ (1 - ((4:ℝ)/25)) * moment 25 (1 - ((4:ℝ)/25)) TPCascade8) := by
        rw [← mul_assoc, e]; ring

lemma mom_one_P : mom 1 (ofHist PPCascade8) = 97566 := by
  rw [mom_one_ofHist]; norm_num [PPCascade8]

lemma card_T : Multiset.card (ofHist TPCascade8) = 10928 := by
  rw [card_ofHist]; decide

theorem gamma : (97566:ℝ) ≤ ((31:ℝ)/32) * (((4:ℕ):ℝ) ^ ((4:ℝ)/25) * mom (1 - ((4:ℝ)/25)) (ofHist TPCascade8)) := by
  have h := scaled_target
  have hu : ((4:ℕ):ℝ) ^ ((4:ℝ)/25) ≤ ((4:ℕ):ℝ) ^ ((4:ℝ)/25) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  calc (97566:ℝ) ≤ ((31:ℝ)/32) * ((25:ℝ) * ((30259301379893:ℝ)/5000000000) / ((503507:ℝ)/500000)) := by norm_num
    _ ≤ ((31:ℝ)/32) * (((4:ℕ):ℝ) ^ ((4:ℝ)/25) * mom (1 - ((4:ℝ)/25)) (ofHist TPCascade8)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ ((31:ℝ)/32) * (((4:ℕ):ℝ) ^ ((4:ℝ)/25) * mom (1 - ((4:ℝ)/25)) (ofHist TPCascade8)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hu (mom_nonneg _ _)

theorem delta : (54640 : ℝ) ≤ ((19:ℝ)/20) * (((4:ℕ):ℝ) ^ ((4:ℝ)/25) * mom (1 - ((4:ℝ)/25)) (ofHist TPCascade8)) := by
  have h := scaled_target
  calc (54640 : ℝ) ≤ ((19:ℝ)/20) * ((25:ℝ) * ((30259301379893:ℝ)/5000000000) / ((503507:ℝ)/500000)) := by norm_num
    _ ≤ ((19:ℝ)/20) * (((4:ℕ):ℝ) ^ ((4:ℝ)/25) * mom (1 - ((4:ℝ)/25)) (ofHist TPCascade8)) := mul_le_mul_of_nonneg_left h (by norm_num)

lemma bernoulli_inv (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (v : ℕ) : (1 - ε) ^ v ≤ 1 / (1 + v * ε) := by
  have hpos : 0 < 1 + (v : ℝ) * ε := by positivity
  rw [le_div_iff₀ hpos]
  have hb : 1 + (v : ℝ) * ε ≤ (1 + ε) ^ v := one_add_mul_le_pow (by linarith) v
  have h2 : (1 - ε) ^ v * (1 + ε) ^ v ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : 0 ≤ (1 - ε) ^ v := pow_nonneg (by linarith) v
  calc (1 - ε) ^ v * (1 + v * ε) ≤ (1 - ε) ^ v * (1 + ε) ^ v := mul_le_mul_of_nonneg_left hb h3
    _ ≤ 1 := h2

theorem final_ineq :
    (1 - ((1:ℝ)/4294967296) : ℝ) ^ 1024 + 2 * ((31:ℝ)/32) ^ 1024 + 2 * ((19:ℝ)/20) ^ 1024 ≤ 1 := by
  have h1 : (1 - ((1:ℝ)/4294967296) : ℝ) ^ 1024 ≤ 1 / (1 + ((1024 : ℕ) : ℝ) * ((1:ℝ)/4294967296)) :=
    bernoulli_inv _ (by norm_num) (by norm_num) 1024
  have h2a : ((31:ℝ)/32) ^ 32 ≤ (1 / 2 : ℝ) := by norm_num
  have h2 : ((31:ℝ)/32) ^ 1024 ≤ (1 / 2 : ℝ) ^ 32 := by
    rw [show (1024 : ℕ) = 32 * 32 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h2a 32
  have h3a : ((19:ℝ)/20) ^ 16 ≤ (1 / 2 : ℝ) := by norm_num
  have h3 : ((19:ℝ)/20) ^ 1024 ≤ (1 / 2 : ℝ) ^ 64 := by
    rw [show (1024 : ℕ) = 16 * 64 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h3a 64
  have h4 : 1 / (1 + ((1024 : ℕ) : ℝ) * ((1:ℝ)/4294967296)) + 2 * (1 / 2 : ℝ) ^ 32 + 2 * (1 / 2 : ℝ) ^ 64 ≤ 1 := by
    norm_num
  generalize (1 - ((1:ℝ)/4294967296) : ℝ) ^ 1024 = A at h1 ⊢
  generalize ((31:ℝ)/32) ^ 1024 = G at h2 ⊢
  generalize ((19:ℝ)/20) ^ 1024 = D at h3 ⊢
  generalize (1 / 2 : ℝ) ^ 32 = H1 at h2 h4
  generalize (1 / 2 : ℝ) ^ 64 = H2 at h3 h4
  generalize 1 / (1 + ((1024 : ℕ) : ℝ) * ((1:ℝ)/4294967296)) = B0 at h1 h4
  linarith

lemma final_combine {x y w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 - ((1:ℝ)/4294967296)) (hy0 : 0 ≤ y) (hy : y ≤ ((31:ℝ)/32))
    (hw0 : 0 ≤ w) (hw : w ≤ ((19:ℝ)/20)) : x ^ 1024 + 2 * y ^ 1024 + 2 * w ^ 1024 ≤ 1 := by
  have h1 := pow_le_pow_left₀ hx0 hx 1024
  have h2 := pow_le_pow_left₀ hy0 hy 1024
  have h3 := pow_le_pow_left₀ hw0 hw 1024
  have h4 := final_ineq
  generalize (1 - ((1:ℝ)/4294967296) : ℝ) ^ 1024 = A at h1 h4
  generalize ((31:ℝ)/32) ^ 1024 = G at h2 h4
  generalize ((19:ℝ)/20) ^ 1024 = D at h3 h4
  linarith

theorem strict :
    mom (1 - ((4:ℝ)/25)) (strictP (ofHist TPCascade8) (ofHist PPCascade8) 1024 (4 ^ 1024) (5 ^ 1024))
      ≤ mom (1 - ((4:ℝ)/25)) (strictT (ofHist TPCascade8) 1024 (5 ^ 1024)) := by
  have hT := T_pos
  have hc : (0 : ℝ) < ((4 : ℕ) : ℝ) ^ ((4:ℝ)/25) := Real.rpow_pos_of_pos (by norm_num) _
  have hden : (0 : ℝ) < ((4 : ℕ) : ℝ) ^ ((4:ℝ)/25) * mom (1 - ((4:ℝ)/25)) (ofHist TPCascade8) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hT
  apply strictify (c := 4) (b := 5) (t := (1 - ((4:ℝ)/25))) (u := ((4:ℝ)/25)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hT
  apply final_combine
  · exact div_nonneg (mom_nonneg _ _) hT.le
  · rw [div_le_iff₀ hT]; exact alpha
  · exact div_nonneg (mom_nonneg _ _) (mul_pos hc hT).le
  · rw [div_le_iff₀ (mul_pos hc hT), mom_one_P]
    exact gamma
  · have hc' : (0 : ℝ) < ((4 : ℕ) : ℝ) ^ (1 - (1 - ((4:ℝ)/25))) := Real.rpow_pos_of_pos (by norm_num) _
    exact div_nonneg (by positivity) (mul_pos hc' hT).le
  · rw [show (1 : ℝ) - (1 - ((4:ℝ)/25)) = ((4:ℝ)/25) by ring, div_le_iff₀ hden, card_T]
    have h := delta
    push_cast at h ⊢
    linarith

end Cascade8
end
end TensorProto
