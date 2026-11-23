import Limit

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace O71

abbrev Space := EuclideanSpace ℝ (Fin 10)

/-- Coordinates in the order c, a₁, b₁, v₁, a₂, b₂, v₂, a₃, b₃, v₃. -/
def physical (w : Space) : Param :=
  (![w 1,w 4,w 7],w 0,w 2,w 8,w 5,![w 3,w 6,w 9])

def center : Space := WithLp.toLp 2 ![0,1,0,0,1,0,0,1,0,0]
def prediction (w : Space) (x : ℝ) := w 0 + w 3 * max (w 1*x+w 2) 0 +
    w 6 * max (w 4*x+w 5) 0 + w 9 * max (w 7*x+w 8) 0

@[simp] theorem prediction_center (x : ℝ) : prediction center x = 0 := by
  simp [prediction,center]

def populationLoss (w : Space) := (∫ x in (-1:ℝ)..1, (prediction w x - prediction center x)^2)/4

theorem physical_loss (w : Space) : loss (physical w) = populationLoss w := by
  simp only [populationLoss,prediction_center,sub_zero]
  rfl

theorem physical_radius (w : Space) : radiusSq (physical w) = dist w center ^ 2 := by
  rw [dist_eq_norm,EuclideanSpace.real_norm_sq_eq]
  simp [radiusSq,physical,center,Fin.sum_univ_succ]
  ring

private theorem extract {n : ℕ} {Y : Type*} [MeasureSpace Y] (i : Fin (n+1))
    (f : (Fin n → ℝ) → Y) (hf : MeasurePreserving f) :
    MeasurePreserving (fun w : Fin (n+1) → ℝ => (w i,f (fun k => w (i.succAbove k)))) :=
  ((MeasurePreserving.id volume).prod hf).comp (volume_preserving_piFinSuccAbove (fun _ => ℝ) i)

private def tripleEquiv : Triple ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0:Fin 3)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ => ℝ)))

private theorem triple_preserving : MeasurePreserving tripleEquiv :=
  ((MeasurePreserving.id volume).prod (volume_preserving_piFinTwo (fun _ => ℝ))).comp
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) (0:Fin 3))

theorem physical_preserving : MeasurePreserving physical := by
  let f := fun w : Fin 10 → ℝ => (w 1,w 4,w 7,w 0,w 2,w 8,w 5,![w 3,w 6,w 9])
  have h : MeasurePreserving f := by
    -- Each index is taken in the tuple left after the preceding extractions.
    have biases := extract (0:Fin 6) _ (extract (3:Fin 5) _
      (extract (1:Fin 4) _ (MeasurePreserving.id volume)))
    have biasAndWeights := extract (0:Fin 7) _ biases
    have he := extract (1:Fin 10) _ (extract (3:Fin 9) _ (extract (5:Fin 8) _ biasAndWeights))
    convert he using 1
    funext w
    repeat' apply Prod.ext
    all_goals try rfl
    funext i; fin_cases i <;> rfl
  let g := fun w : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × Triple =>
    (tripleEquiv.symm (w.1,w.2.1,w.2.2.1),w.2.2.2)
  have hg : MeasurePreserving g :=
    (triple_preserving.symm.prod (MeasurePreserving.id volume)).comp
      (volume_preserving_prodAssoc.symm.comp ((MeasurePreserving.id volume).prod volume_preserving_prodAssoc.symm))
  convert hg.comp (h.comp (PiLp.volume_preserving_ofLp (Fin 10))) using 1
  funext w
  apply Prod.ext
  swap; · rfl
  apply tripleEquiv.injective
  change tripleEquiv _ = tripleEquiv (g (f (WithLp.ofLp w))).1
  rw [show (g (f (WithLp.ofLp w))).1 = tripleEquiv.symm (w 1,w 4,w 7) by rfl,
    MeasurableEquiv.apply_symm_apply]
  rfl

def physicalSublevel (e : ℝ) : Set Space :=
  Metric.closedBall center (1/3) ∩ {w | populationLoss w ≤ e}

theorem physicalSublevel_volume (e : ℝ) : volume (physicalSublevel e) = volume (sublevel e) := by
  have h : physicalSublevel e = physical ⁻¹' sublevel e := by
    ext w
    change (dist w center ≤ 1/3 ∧ populationLoss w ≤ e) ↔ radiusSq (physical w) ≤ 1/9 ∧ loss (physical w) ≤ e
    rw [physical_radius,physical_loss]
    constructor <;> rintro ⟨hd,hk⟩ <;> refine ⟨?_,hk⟩ <;> nlinarith only [hd,dist_nonneg (x := w) (y := center)]
  rw [h,physical_preserving.measure_preimage (sublevel_measurable _).nullMeasurableSet]

/-- Theorem A for ordinary Lebesgue volume on the literal Euclidean closed ball in ℝ¹⁰. -/
theorem theorem_A : ∃ C : ℝ, 0 < C ∧
    Tendsto (fun e : ℝ => (volume (physicalSublevel e)).toReal / e^(11/6 : ℝ)) (𝓝[>] 0) (𝓝 C) := by
  simpa only [physicalSublevel_volume,volumeLaw] using volume_asymptotic

#print axioms theorem_A
end O71
