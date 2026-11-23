import Model

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace O71

/-- Regular formula for the loss divided by q⁶ when the loss threshold is q⁶. -/
def scaledEnergy (q c t D p z S B : ℝ) :=
  let d := q^2*D
  let n := c+B+S*(t+d)
  let m := q*(c+p*(B+S*(t+d)))-z*p*(1-p)*D
  ((1+t)*3*c^2 + p*D*mass (q*c) m + (1-p)*D*mass m (q*n) +
    (1-(t+d))*mass n (c+B+S))/12

theorem energy_scale (q c t D p z S B : ℝ) :
    energy (q^3*c) t (q^2*D) p z (q^3*S) (q^3*B) =
    q^6*scaledEnergy q c t D p z S B := by
  unfold energy midVal endVal scaledEnergy mass
  ring

theorem scaledEnergy_zero (c t D p z S B : ℝ) :
    scaledEnergy 0 c t D p z S B =
    ((1+t)*3*c^2+(1-t)*mass (c+B+S*t) (c+B+S) + (z*p*(1-p))^2*D^3)/12 := by
  unfold scaledEnergy mass; ring

/-- Continuous extension of the physical parameters to q = 0 at nonzero a and D. -/
def regularChart (q : ℝ) (a : Triple) (c t D p z S B : ℝ) : Param :=
  let d := q^2*D
  let l := q*(B+S*(t+d))/D-z*(1-p)
  (a,q^3*c,-a 0*t,-a 2*(t+d),-a 1*(t+p*d),
    ![l/a 0,z/a 1,(q^3*S-l-z)/a 2])

theorem chart_regular (q : ℝ) (a : Triple) (c t D p z S B : ℝ) (hq : q ≠ 0) (hD : D ≠ 0) :
    chart a (q^3*c) t (q^2*D) p z (q^3*S) (q^3*B) = regularChart q a c t D p z S B := by
  have he : leftJump t (q^2*D) p z (q^3*S) (q^3*B) = q*(B+S*(t+q^2*D))/D-z*(1-p) := by
    unfold leftJump; field_simp [hq,hD]
  simp [chart,regularChart,rightJump,he]

@[fun_prop] theorem radiusSq_continuous : Continuous radiusSq := by unfold radiusSq; fun_prop
@[fun_prop] theorem loss_continuous : Continuous loss := by
  unfold loss
  apply Continuous.div_const
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry net
  fun_prop

theorem sublevel_measurable (e : ℝ) : MeasurableSet (sublevel e) :=
  (measurableSet_le radiusSq_continuous.measurable measurable_const).inter
    (measurableSet_le loss_continuous.measurable measurable_const)

def regular (q : ℝ) (x : Param) : Param :=
  let (a,c,t,D,p,v) := x
  regularChart q a c t D p (v 0) (v 1) (v 2)

def normalizedLoss (q : ℝ) (x : Param) : ℝ :=
  let (_,c,t,D,p,v) := x
  scaledEnergy q c t D p (v 0) (v 1) (v 2)

@[fun_prop] theorem normalizedLoss_cont : Continuous (fun w : ℝ × Param => normalizedLoss w.1 w.2) := by
  unfold normalizedLoss scaledEnergy mass; fun_prop

theorem regular_cont (w : ℝ × Param) (ha : ∀ i, w.2.1 i ≠ 0) (hD : w.2.2.2.2.1 ≠ 0) :
    ContinuousAt (fun w : ℝ × Param => regular w.1 w.2) w := by
  unfold regular regularChart
  fun_prop (disch := first | exact ha _ | exact hD)

theorem loss_scale (q : ℝ) (w : Param) (hq : 0 < q) (ha : ∀ i, 0 < w.1 i)
    (hl : -1 ≤ w.2.2.1) (hD : 0 < w.2.2.2.1) (hp : w.2.2.2.2.1 ∈ Icc 0 1)
    (hr : w.2.2.1+q^2*w.2.2.2.1 ≤ 1) :
    loss (regular q w) = q^6 * normalizedLoss q w := by
  rcases w with ⟨a,c,t,D,p,v⟩
  dsimp [regular,normalizedLoss] at *
  rw [← chart_regular _ _ _ _ _ _ _ _ _ hq.ne' hD.ne',
    loss_chart a ha _ _ _ _ _ _ _ hl (mul_pos (sq_pos_of_pos hq) hD) hp.1 hp.2 hr, energy_scale]

end O71
