import Mathlib

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval

namespace O71

abbrev Triple := Fin 3 → ℝ
-- (input slopes, output bias, three biases in physical order 1,3,2, three output weights)
abbrev Param := Triple × ℝ × ℝ × ℝ × ℝ × Triple

def radiusSq (w : Param) : ℝ :=
  (∑ j, (w.1 j - 1)^2) + w.2.1^2 + w.2.2.1^2 + w.2.2.2.1^2 + w.2.2.2.2.1^2 +
  ∑ j, w.2.2.2.2.2 j ^ 2

def net (w : Param) (x : ℝ) : ℝ :=
  let (a,c,b₁,b₃,b₂,v) := w
  c + v 0 * max (a 0*x+b₁) 0 + v 1 * max (a 1*x+b₂) 0 + v 2 * max (a 2*x+b₃) 0

def loss (w : Param) : ℝ := (∫ x in (-1:ℝ)..1, net w x ^ 2) / 4
def sublevel (e : ℝ) : Set Param := {w | radiusSq w ≤ 1/9 ∧ loss w ≤ e}
def volumeLaw : Prop := ∃ C : ℝ, 0 < C ∧
  Tendsto (fun e : ℝ => (volume (sublevel e)).toReal / e ^ (11/6 : ℝ)) (𝓝[>] 0) (𝓝 C)

def spline (c t d p l z r x : ℝ) : ℝ :=
  c + l * max (x-t) 0 + z * max (x-(t+p*d)) 0 + r * max (x-(t+d)) 0

def leftJump (t d p z S B : ℝ) := (B+S*(t+d))/d-z*(1-p)
def rightJump (t d p z S B : ℝ) := S-leftJump t d p z S B-z
def chart (a : Triple) (c t d p z S B : ℝ) : Param :=
  (a,c,-a 0*t,-a 2*(t+d),-a 1*(t+p*d),
    ![leftJump t d p z S B / a 0, z / a 1, rightJump t d p z S B / a 2])

theorem relu_scale (a v t x : ℝ) (ha : 0 < a) :
    v/a * max (a*x + -a*t) 0 = v * max (x-t) 0 := by
  rw [show a*x + -a*t = a*(x-t) by ring, ← mul_zero a, ← mul_max_of_nonneg _ _ ha.le]
  field_simp; simp

theorem net_chart (a : Triple) (ha : ∀ i, 0 < a i) (c t d p z S B x : ℝ) :
    net (chart a c t d p z S B) x =
    spline c t d p (leftJump t d p z S B) z (rightJump t d p z S B) x := by
  change _ + _ / _ * _ + _ / _ * _ + _ / _ * _ = _
  rw [relu_scale _ _ _ _ (ha 0), relu_scale _ _ _ _ (ha 1), relu_scale _ _ _ _ (ha 2)]
  rfl

/-- Three times the mean squared value of a linear segment with endpoint values u,v. -/
def mass (u v : ℝ) := u^2+u*v+v^2

theorem segment (A B L R : ℝ) :
    (∫ x in L..R, (A+B*x)^2) = (R-L)*mass (A+B*L) (A+B*R)/3 := by
  let F := fun x : ℝ => A^2*x+A*B*x^2+B^2*x^3/3
  calc
    _ = F R - F L := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        dsimp [F]
        have linear := (hasDerivAt_id x).const_mul (A^2)
        have quadratic := ((hasDerivAt_id x).pow 2).const_mul (A*B)
        have cubic := (((hasDerivAt_id x).pow 3).const_mul (B^2)).div_const 3
        convert! (linear.add quadratic).add cubic using 1
        simp only [id_eq]
        ring
      · exact Continuous.intervalIntegrable (by fun_prop) ..
    _ = _ := by dsimp [F,mass]; ring

def midVal (c t d p z S B : ℝ) := c + p*(B+S*(t+d)) - z*p*(1-p)*d
def endVal (c t d S B : ℝ) := c+B+S*(t+d)

def energy (c t d p z S B : ℝ) :=
  let m := midVal c t d p z S B
  let n := endVal c t d S B
  ((1+t)*3*c^2 + p*d*mass c m + (1-p)*d*mass m n +
    (1-(t+d))*mass n (c+B+S))/12

private theorem affinePiece (f : ℝ → ℝ) (L R A B : ℝ) (h : L ≤ R)
    (hf : ∀ x ∈ Icc L R, f x = A+B*x) :
    (∫ x in L..R, f x ^ 2) = (R-L)*mass (A+B*L) (A+B*R)/3 := by
  rw [← segment]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [hf x (by simpa [uIcc_of_le h] using hx)]

theorem loss_chart (a : Triple) (ha : ∀ i, 0 < a i) (c t d p z S B : ℝ)
    (hl : -1 ≤ t) (hd : 0 < d) (hp : 0 ≤ p) (hq : p ≤ 1) (hr : t+d ≤ 1) :
    loss (chart a c t d p z S B) = energy c t d p z S B := by
  let l := leftJump t d p z S B
  let r := rightJump t d p z S B
  let f := spline c t d p l z r
  have hf : Continuous f := by unfold f spline; fun_prop
  have hi (x y : ℝ) : IntervalIntegrable (fun x => f x ^ 2) volume x y := (hf.pow 2).intervalIntegrable (μ := volume) x y
  have h₁ : t ≤ t+p*d := by nlinarith
  have h₂ : t+p*d ≤ t+d := by nlinarith
  have e₁ := affinePiece f (-1) t c 0 hl (by
    intro x hx
    simp [f,spline,max_eq_right (sub_nonpos.mpr hx.2),
      max_eq_right (sub_nonpos.mpr (hx.2.trans h₁)), max_eq_right (sub_nonpos.mpr (hx.2.trans (h₁.trans h₂)))])
  have e₂ := affinePiece f t (t+p*d) (c-l*t) l h₁ (by
    intro x hx
    simp [f,spline,max_eq_left (sub_nonneg.mpr hx.1), max_eq_right (sub_nonpos.mpr hx.2),
      max_eq_right (sub_nonpos.mpr (hx.2.trans h₂))]; ring)
  have e₃ := affinePiece f (t+p*d) (t+d) (c-l*t-z*(t+p*d)) (l+z) h₂ (by
    intro x hx
    simp [f,spline,max_eq_left (sub_nonneg.mpr (h₁.trans hx.1)),max_eq_left (sub_nonneg.mpr hx.1),
      max_eq_right (sub_nonpos.mpr hx.2)]; ring)
  have e₄ := affinePiece f (t+d) 1 (c+B) S hr (by
    intro x hx
    simp only [f,spline,max_eq_left (sub_nonneg.mpr ((h₁.trans h₂).trans hx.1)),
      max_eq_left (sub_nonneg.mpr (h₂.trans hx.1)),max_eq_left (sub_nonneg.mpr hx.1)]
    dsimp [l,r,rightJump,leftJump]; field_simp; ring)
  unfold loss
  simp_rw [net_chart a ha]
  change (∫ x in (-1:ℝ)..1, f x ^ 2) / 4 = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-1) (t+d)) (hi (t+d) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-1) (t+p*d)) (hi (t+p*d) (t+d)),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-1) t) (hi t (t+p*d)), e₁,e₂,e₃,e₄]
  have hm : l*d = B+S*(t+d)-z*(1-p)*d := by dsimp [l,leftJump]; field_simp
  simp only [zero_mul,add_zero,mul_one]
  have e (x : ℝ) : c-l*t+l*(t+x*d) = c+x*(l*d) := by ring
  have e' (x : ℝ) : c-l*t-z*(t+p*d)+(l+z)*(t+x*d) = c+x*(l*d)+z*(x-p)*d := by ring
  rw [e p, e' p, show c-l*t-z*(t+p*d)+(l+z)*(t+d) = c+l*d+z*(1-p)*d by ring, hm]
  dsimp [energy,endVal,midVal,mass]; ring

end O71
