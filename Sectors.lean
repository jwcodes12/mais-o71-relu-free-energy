import LowerBound

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace O71

def knots (w : Param) : Triple :=
  ![-w.2.2.1/w.1 0,-w.2.2.2.2.1/w.1 1,-w.2.2.2.1/w.1 2]

def sector (strict : Bool) (e : ℝ) : Set Param := {w | w ∈ sublevel e ∧
  if strict then knots w 0 < knots w 1 ∧ knots w 1 < knots w 2
  else knots w 0 ≤ knots w 1 ∧ knots w 1 ≤ knots w 2}

theorem sector_measurable (s : Bool) (e : ℝ) : MeasurableSet (sector s e) := by
  have h (i : Fin 3) : Measurable (fun w => knots w i) := by unfold knots; fun_prop
  cases s
  · exact (sublevel_measurable e).inter ((measurableSet_le (h 0) (h 1)).inter (measurableSet_le (h 1) (h 2)))
  · exact (sublevel_measurable e).inter ((measurableSet_lt (h 0) (h 1)).inter (measurableSet_lt (h 1) (h 2)))

abbrev Raw := Triple × ℝ × Triple × Triple

def pack (x : Raw) : Param := (x.1,x.2.1,x.2.2.1 0,x.2.2.1 2,x.2.2.1 1,x.2.2.2)
theorem pack_preserving : MeasurePreserving pack := by
  have h : MeasurePreserving (fun b : Triple => (b 0,b 2,b 1)) := by
    exact ((MeasurePreserving.id volume).prod (measurePreserving_swap.comp
      (volume_preserving_piFinTwo (fun _ => ℝ)))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
  have h' : MeasurePreserving (fun x : Triple × Triple => (x.1 0,x.1 2,x.1 1,x.2)) :=
    ((MeasurePreserving.id volume).prod volume_preserving_prodAssoc).comp
      (volume_preserving_prodAssoc.comp (h.prod (MeasurePreserving.id volume)))
  exact (MeasurePreserving.id volume).prod ((MeasurePreserving.id volume).prod h')

abbrev Perm := Equiv.Perm (Fin 3)
def relabel (σ : Perm) (x : Raw) : Raw := (x.1 ∘ σ,x.2.1,x.2.2.1 ∘ σ,x.2.2.2 ∘ σ)
theorem relabel_preserving (σ : Perm) : MeasurePreserving (relabel σ) := by
  have h : MeasurePreserving (fun v : Triple => v ∘ σ) := by
    convert volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) σ.symm using 1
    ext v i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  exact h.prod ((MeasurePreserving.id volume).prod (h.prod h))

theorem pack_radius (x : Raw) : radiusSq (pack x) =
    (∑ i, (x.1 i - 1)^2) + x.2.1^2 + (∑ i, (x.2.2.1 i)^2) + ∑ i, (x.2.2.2 i)^2 := by
  simp [pack,radiusSq,Fin.sum_univ_three]; ring

theorem pack_net (w : Raw) (x : ℝ) : net (pack w) x = w.2.1 +
    ∑ i, w.2.2.2 i * max (w.1 i*x+w.2.2.1 i) 0 := by simp [net,pack,Fin.sum_univ_three]; ring

theorem relabel_sublevel (σ : Perm) (w : Raw) (e : ℝ) :
    pack (relabel σ w) ∈ sublevel e ↔ pack w ∈ sublevel e := by
  have hN : net (pack (relabel σ w)) = net (pack w) := by
    funext x
    rw [pack_net,pack_net]
    exact congrArg (w.2.1+·) (Equiv.sum_comp σ (fun i => w.2.2.2 i * max (w.1 i*x+w.2.2.1 i) 0))
  change radiusSq _ ≤ _ ∧ loss _ ≤ _ ↔ radiusSq _ ≤ _ ∧ loss _ ≤ _
  have hL : loss (pack (relabel σ w)) = loss (pack w) := by unfold loss; rw [hN]
  rw [hL,pack_radius,pack_radius]
  simp only [relabel,Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i => (w.1 i-1)^2),Equiv.sum_comp σ (fun i => (w.2.2.1 i)^2),
    Equiv.sum_comp σ (fun i => (w.2.2.2 i)^2)]

def rawKnots (w : Raw) : Triple := fun i => -w.2.2.1 i / w.1 i

theorem mem_sector_raw (s : Bool) (e : ℝ) (σ : Perm) (w : Raw) :
    pack (relabel σ w) ∈ sector s e ↔ pack w ∈ sublevel e ∧
      (if s then StrictMono (rawKnots w ∘ σ) else Monotone (rawKnots w ∘ σ)) := by
  unfold sector
  simp only [mem_ofPred_eq,relabel_sublevel]
  apply and_congr_right; intro _
  cases s
  · change (_ ≤ _ ∧ _ ≤ _) ↔ Monotone _
    rw [Fin.monotone_iff_le_succ]
    exact ⟨fun h i => by fin_cases i <;> first | exact h.1 | exact h.2,
      fun h => ⟨h 0,h 1⟩⟩
  · change (_ < _ ∧ _ < _) ↔ StrictMono _
    rw [Fin.strictMono_iff_lt_succ]
    exact ⟨fun h i => by fin_cases i <;> first | exact h.1 | exact h.2,
      fun h => ⟨h 0,h 1⟩⟩

theorem sector_sandwich (e : ℝ) :
    6 * volume (sector true e) ≤ volume (sublevel e) ∧
    volume (sublevel e) ≤ 6 * volume (sector false e) := by
  let A (s : Bool) (σ : Perm) := (pack ∘ relabel σ) ⁻¹' sector s e
  have hm (s : Bool) (σ : Perm) : MeasurableSet (A s σ) :=
    (sector_measurable _ _).preimage (pack_preserving.comp (relabel_preserving σ)).measurable
  have hv (s : Bool) (σ : Perm) : volume (A s σ) = volume (sector s e) :=
    (pack_preserving.comp (relabel_preserving σ)).measure_preimage (sector_measurable _ _).nullMeasurableSet
  have he := pack_preserving.measure_preimage (sublevel_measurable e).nullMeasurableSet
  rw [← he]
  have hsub : (⋃ σ, A true σ) ⊆ pack ⁻¹' sublevel e := by
    intro w hw
    obtain ⟨σ,hσ⟩ := mem_iUnion.mp hw
    exact ((mem_sector_raw true e σ w).mp hσ).1
  have hsup : pack ⁻¹' sublevel e ⊆ ⋃ σ, A false σ := by
    intro w hw
    exact mem_iUnion.mpr ⟨_,(mem_sector_raw false e (Tuple.sort (rawKnots w)) w).mpr
      ⟨hw,Tuple.monotone_sort _⟩⟩
  have hd : Pairwise (fun i j => Disjoint (A true i) (A true j)) := by
    intro σ τ hst
    apply Set.disjoint_left.mpr
    intro w hσ hτ
    have h (π : Perm) (hπ : w ∈ A true π) : π = Tuple.sort (rawKnots w) := by
      have H : StrictMono (rawKnots w ∘ π) := ((mem_sector_raw true e π w).mp hπ).2
      exact Tuple.eq_sort_iff.mpr ⟨H.monotone,fun i j hij hbad => ((H hij).ne hbad).elim⟩
    exact hst ((h _ hσ).trans (h _ hτ).symm)
  have card : Fintype.card Perm = 6 := by decide
  constructor
  · have H := measure_mono hsub (μ := volume)
    rw [measure_iUnion hd (hm _)] at H
    simpa [hv,tsum_fintype,card,nsmul_eq_mul] using H
  · exact (measure_mono hsup).trans (by
      apply (measure_iUnion_le _).trans
      simp [hv,tsum_fintype,card,nsmul_eq_mul])

end O71
