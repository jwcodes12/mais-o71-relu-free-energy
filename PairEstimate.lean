import Quantitative

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal Topology
namespace O71

def sampleSize (k : ℕ) := (k+1)^6
def scale (k : ℕ) : ℝ := ((k:ℝ)+1)⁻¹
theorem scale_pos (k : ℕ) : 0 < scale k := by unfold scale; positivity
theorem scale_limit : Tendsto scale atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
theorem scale_id (k : ℕ) : (sampleSize k : ℝ)*(scale k)^6 = 1 := by
  simp [sampleSize,scale, Nat.cast_add,pow_ne_zero,show (k:ℝ)+1 ≠ 0 by positivity]
def pairKernel (k : ℕ) (z : Param × Param) :=
  (∫⁻ x, eexp (chartNet (scale k) z.1 x * chartNet (scale k) z.2 x) ∂inputLaw)^(sampleSize k)

theorem pair_bounds {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, ∀ᶠ k in atTop, ∀ z ∈ box L ×ˢ box L,
      pairKernel k z ≤ eexp C ∧
      (2*(1+L)*(scale k)^2 < |coordT z.1-coordT z.2| → pairKernel k z ≤ eexp 99) := by
  let J := 1+L
  let A := 7+2*J
  refine ⟨98+4*A^2*J,?_⟩
  have ev (f : ℝ → ℝ) (hf : Continuous f) (v : ℝ) (hv : f 0 < v) :
      ∀ᶠ k in atTop, f (scale k) < v := ((hf.tendsto 0).comp scale_limit).eventually_lt tendsto_const_nhds hv
  filter_upwards [ev id continuous_id 1 (by norm_num),
    ev (fun q => q^2*J) (by fun_prop) small (by norm_num),
    ev (fun q => 49*q^6) (by fun_prop) 1 (by norm_num),
    ev (fun q => A^2*q^4) (by fun_prop) 1 (by norm_num),
    ev (fun q => 7*A*q^5) (by fun_prop) 1 (by norm_num),
    ev (fun q => 28*A*J*q) (by fun_prop) 1 (by norm_num)]
    with k hk hd ha hb hbf hcross
  dsimp only [id_eq] at hk hd ha hb hbf hcross
  intro z hz
  let q := scale k
  have hq : 0 < q := scale_pos k
  have h := quantitative_pair (sampleSize k) hL hq hk.le hd.le ha.le hb.le hbf.le hcross.le z hz
  simpa only [q,scale_id,one_mul,pairKernel,chartKernel,A,J] using h
end O71
