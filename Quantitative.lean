import Box
import KernelBound

noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal Topology
namespace O71

def chartKernel (n : ℕ) (q : ℝ) (z : Param × Param) :=
  (∫⁻ x, eexp (chartNet q z.1 x * chartNet q z.2 x) ∂inputLaw)^n

theorem quantitative_pair (n : ℕ) {q L : ℝ} (hL : 0 < L) (hq : 0 < q) (hk : q ≤ 1)
    (hd : q^2*(1+L) ≤ small) (ha : 49*q^6 ≤ 1)
    (hb : (7+2*(1+L))^2*q^4 ≤ 1) (hbf : 7*(7+2*(1+L))*q^5 ≤ 1)
    (hcross : 28*(7+2*(1+L))*(1+L)*q ≤ 1) :
    ∀ z ∈ box L ×ˢ box L, chartKernel n q z ≤ eexp (n*q^6*(98+4*(7+2*(1+L))^2*(1+L))) ∧
      (2*(1+L)*q^2 < |coordT z.1-coordT z.2| → chartKernel n q z ≤ eexp (n*q^6*99)) := by
  let J := 1+L
  let A := 7+2*J
  have hJ : 0 ≤ J := by dsimp [J]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  change 28*A*J*q ≤ 1 at hcross
  intro z hz
  let U (w : Param) := Icc (coordT w) (coordT w+q^2*J)
  have H1 := box_geometry hq hk hd hz.1
  have H2 := box_geometry hq hk hd hz.2
  let f := chartNet q z.1
  let g := chartNet q z.2
  have hU : inputLaw (U z.1 ∪ U z.2) ≤ ENNReal.ofReal (2*(q^2*J)) := calc
    _ ≤ _ := measure_union_le .. 
    _ ≤ ENNReal.ofReal (q^2*J)+ENNReal.ofReal (q^2*J) := add_le_add (input_interval _ _ (mul_nonneg (sq_nonneg q) hJ)) (input_interval _ _ (mul_nonneg (sq_nonneg q) hJ))
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity),two_mul]
  have hoff (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) (hu : x ∉ U z.1 ∪ U z.2) : f x*g x ≤ 49*q^6 := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    have h := mul_le_mul ((H1.2 x hx).2 (fun h => hu (.inl h))) ((H2.2 x hx).2 (fun h => hu (.inr h))) (abs_nonneg _) (by positivity)
    convert h using 1; ring
  have calcBound (b : ℝ) (h₀ : 0 ≤ b) (h₁ : b ≤ 1)
      (h : ∀ x ∈ Icc (-1:ℝ) 1, x ∈ U z.1 ∪ U z.2 → f x*g x ≤ b) :
      chartKernel n q z ≤ eexp (n*(2*(49*q^6)+2*b*(2*(q^2*J)))) :=
    kernel_bound (measurableSet_Icc.union measurableSet_Icc) hU (by positivity)
      ⟨by positivity,ha⟩ ⟨h₀,h₁⟩ hoff h
  constructor
  · have hh := calcBound (A^2*q^4) (by positivity) hb (by
      intro x hx _
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      have hh := mul_le_mul (H1.2 x hx).1 (H2.2 x hx).1 (abs_nonneg _) (by positivity)
      change _ ≤ A*q^2*(A*q^2) at hh
      convert hh using 1; ring)
    convert hh using 2
    ring
  · intro hsep
    have hh := calcBound (7*A*q^5) (by positivity) hbf (by
      intro x hx _
      have hor : x ∉ U z.1 ∨ x ∉ U z.2 := by
        by_contra! H
        obtain ⟨h1,h2⟩ := H
        have h11 := h1.1; have h12 := h1.2
        have h21 := h2.1; have h22 := h2.2
        change _ ≤ coordT z.1+q^2*J at h12
        change _ ≤ coordT z.2+q^2*J at h22
        change 2*J*q^2 < _ at hsep
        rcases lt_abs.mp hsep with h|h <;> nlinarith [sq_nonneg q]
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      rcases hor with h|h
      · have H := mul_le_mul ((H1.2 x hx).2 h) (H2.2 x hx).1 (abs_nonneg _) (by positivity)
        change _ ≤ 7*q^3*(A*q^2) at H
        convert H using 1; ring
      · have H := mul_le_mul (H1.2 x hx).1 ((H2.2 x hx).2 h) (abs_nonneg _) (by positivity)
        change _ ≤ A*q^2*(7*q^3) at H
        convert H using 1; ring)
    refine hh.trans (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_))
    calc
      _ = ((n : ℝ)*q^6)*(98+28*A*J*q) := by ring
      _ ≤ _ := by gcongr; linarith only [hcross]

end O71
