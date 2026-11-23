import Likelihood

noncomputable section
open MeasureTheory Filter Set Real
open scoped ENNReal Topology
namespace O71

def boundedInProbability (R : (n : ℕ) → Sample n → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ, ∀ᶠ n in atTop, (sampleLaw n).real {s | M < |R n s|} ≤ η

def boundedAboveInProbability (R : (n : ℕ) → Sample n → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ, ∀ᶠ n in atTop, (sampleLaw n).real {s | M < R n s} ≤ η

def displayOne (a : ℝ) (m : ℕ) (C : ℝ) : Prop :=
  Tendsto (fun e : ℝ => ((volume (physicalSublevel e)).toReal / (volume ballW).toReal) /
    (e^a * (log (1/e))^(m-1))) (𝓝[>] 0) (𝓝 C)

def residual (a : ℝ) (m : ℕ) (n : ℕ) (s : Sample n) :=
  excess s - a*log n + ((m-1 : ℕ) : ℝ)*log (log n)

def theoremBStatement := boundedAboveInProbability fun n s =>
  residual (11/6) 1 n s + (1/3)*log (log n)

def sharedDisplays := ∃ (a : ℝ) (m : ℕ) (C : ℝ),
  0 < a ∧ 1 ≤ m ∧ 0 < C ∧ displayOne a m C ∧ boundedInProbability (residual a m)

theorem prior_unique {a C : ℝ} {m : ℕ} (hm : 1 ≤ m) (hC : 0 < C) (h : displayOne a m C) :
    a = 11/6 ∧ m = 1 := by
  let V := (volume ballW).toReal
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_closedBall_pos volume _ (by norm_num)).ne'
    (isCompact_closedBall _ _).measure_ne_top
  apply display_one_unique a (C*V) m hm (mul_pos hC hV)
  apply (h.mul_const V).congr
  intro e
  dsimp [V] at *
  field_simp [hV.ne']

def escapesLeft (R : (n : ℕ) → Sample n → ℝ) :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℝ, ∃ᶠ n in atTop, δ ≤ (sampleLaw n).real {s | R n s < -M}

theorem refutation_of_escape (h : escapesLeft (residual (11/6) 1)) : ¬ sharedDisplays := by
  rintro ⟨a,m,C,_,hm,hC,h1,h2⟩
  obtain ⟨rfl,rfl⟩ := prior_unique hm hC h1
  obtain ⟨δ,hδ,h⟩ := h
  obtain ⟨M,hM⟩ := h2 (δ/2) (by positivity)
  obtain ⟨n,hn,hb⟩ := ((h M).and_eventually hM).exists
  have hle : (sampleLaw n).real {s | residual (11/6) 1 n s < -M} ≤
      (sampleLaw n).real {s | M < |residual (11/6) 1 n s|} :=
    measureReal_mono (fun s hs => by
      change residual _ _ _ _ < -M at hs
      change M < |residual (11/6) 1 n s|
      linarith [neg_le_abs (residual (11/6) 1 n s)])
  linarith

theorem divergence_of_theoremB (h : theoremBStatement) (T η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, (sampleLaw n).real {s | T ≤ residual (11/6) 1 n s} ≤ η := by
  obtain ⟨M,hM⟩ := h η hη
  have ht : Tendsto (fun n : ℕ => log (log n)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hM,ht.eventually_gt_atTop (3*(M-T))] with n hn hg
  refine le_trans (measureReal_mono (s₂ := {s | M < residual (11/6) 1 n s +
    1/3*log (log n)}) ?_) hn
  intro s hs
  change T ≤ residual (11/6) 1 n s at hs
  change M < residual (11/6) 1 n s + _
  linarith

theorem refutation_of_theoremB (h : theoremBStatement) : ¬ sharedDisplays := by
  apply refutation_of_escape
  refine ⟨1/2,by norm_num,fun M => Filter.Eventually.frequently ?_⟩
  filter_upwards [divergence_of_theoremB h (-M) (1/2) (by norm_num)] with n hn
  have hm : Measurable (fun s : Sample n => residual (11/6) 1 n s) := by
    unfold residual excess evidence likelihood ratio eexp prediction
    fun_prop
  have hc := probReal_compl_eq_one_sub (μ := sampleLaw n)
    (measurableSet_le measurable_const hm (f := fun _ => -M))
  rw [show {s | -M ≤ residual (11/6) 1 n s}ᶜ = {s | residual (11/6) 1 n s < -M} by
    ext; simp] at hc
  linarith

#print axioms refutation_of_theoremB
end O71
