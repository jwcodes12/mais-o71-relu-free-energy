import Display

noncomputable section
open MeasureTheory Set Filter Real
namespace O71

def ramp (t d x : ℝ) := (max (x-t) 0 - max (x-(t+d)) 0)/d
def bump (t d p x : ℝ) :=
  max (x-(t+p*d)) 0 - (1-p)*max (x-t) 0 - p*max (x-(t+d)) 0

theorem ramp_bounds {t d x : ℝ} (hd : 0 < d) : 0 ≤ ramp t d x ∧ ramp t d x ≤ 1 := by
  unfold ramp
  constructor
  · exact div_nonneg (sub_nonneg.mpr (max_le_max_right 0 (by linarith : x-(t+d) ≤ x-t))) hd.le
  · rw [div_le_one hd]
    rcases le_total x t with h|h
    · rw [max_eq_right (by linarith : x-t ≤ 0)]; linarith [le_max_right (x-(t+d)) 0]
    · rw [max_eq_left (by linarith : 0 ≤ x-t)]; linarith [le_max_left (x-(t+d)) 0]

theorem bump_off {t d p x : ℝ} (hd : 0 ≤ d) (hp : p ∈ Icc 0 1)
    (hx : x ∉ Icc t (t+d)) : bump t d p x = 0 := by
  have hh := mul_nonneg hp.1 hd
  have hj := mul_le_of_le_one_left hd hp.2
  rw [mem_Icc,not_and_or] at hx
  rcases hx with h|h
  · simp [bump,max_eq_right (by linarith : x-t ≤ 0),
      max_eq_right (by linarith : x-(t+p*d) ≤ 0), max_eq_right (by linarith : x-(t+d) ≤ 0)]
  · simp only [bump,max_eq_left (by linarith : 0 ≤ x-t),
      max_eq_left (by linarith : 0 ≤ x-(t+p*d)),max_eq_left (by linarith : 0 ≤ x-(t+d))]
    ring

theorem bump_bound {t d p x : ℝ} (hd : 0 ≤ d) (hp : p ∈ Icc 0 1) :
    |bump t d p x| ≤ 2*d := by
  by_cases hx : x ∈ Icc t (t+d)
  · have h1 := hx.1
    have h2 := hx.2
    have h3 := mul_nonneg hp.1 hd
    have h4 := mul_le_of_le_one_left (sub_nonneg.mpr h1) (by linarith [hp.1] : 1-p ≤ 1)
    have h5 := mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr h1)
    unfold bump
    rw [max_eq_right (by linarith : x-(t+d) ≤ 0),max_eq_left (by linarith : 0 ≤ x-t)]
    have hm : max (x-(t+p*d)) 0 ≤ d := max_le (by linarith) hd
    rw [abs_le]; constructor <;> linarith [le_max_right (x-(t+p*d)) 0]
  · rw [bump_off hd hp hx,abs_zero]; positivity

theorem chart_split (a : Triple) (ha : ∀ i, 0 < a i) (c t d p z S B x : ℝ) (hd : d ≠ 0) :
    net (chart a c t d p z S B) x =
      c + (B+S*(t+d))*ramp t d x + S*max (x-(t+d)) 0 + z*bump t d p x := by
  rw [net_chart a ha]
  unfold spline ramp bump rightJump leftJump
  field_simp; ring

theorem macro_bound {q c t d S B x : ℝ} (hq : 0 ≤ q) (hd : 0 < d) (hd' : d ≤ 1)
    (ht : |t| ≤ 1) (hx : |x| ≤ 1) (hc : |c| ≤ q^3) (hS : |S| ≤ q^3) (hB : |B| ≤ q^3) :
    |c + (B+S*(t+d))*ramp t d x + S*max (x-(t+d)) 0| ≤ 7*q^3 := by
  have ht' := abs_le.mp ht
  have hx' := abs_le.mp hx
  have htd : |t+d| ≤ 2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hr := ramp_bounds (t := t) (x := x) hd
  have hs : |S*(t+d)| ≤ q^3*2 := by rw [abs_mul]; gcongr
  have hbr : |(B+S*(t+d))*ramp t d x| ≤ (q^3+q^3*2)*1 := by
    rw [abs_mul,abs_of_nonneg hr.1]
    exact mul_le_mul ((abs_add_le ..).trans (add_le_add hB hs)) hr.2 hr.1 (by positivity)
  have hj : |S*max (x-(t+d)) 0| ≤ q^3*3 := by
    rw [abs_mul,abs_of_nonneg (le_max_right (x-(t+d)) 0)]
    exact mul_le_mul hS (max_le (by linarith) (by norm_num)) (le_max_right _ _) (by positivity)
  linarith [abs_add_le c ((B+S*(t+d))*ramp t d x),
    abs_add_le (c+(B+S*(t+d))*ramp t d x) (S*max (x-(t+d)) 0)]

end O71
