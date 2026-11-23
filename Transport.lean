import Model

noncomputable section
open MeasureTheory Set Matrix
open scoped ENNReal
namespace O71

/-- A change of variables for every nonnegative measurable test function. -/
def HasVolumeFactor {X : Type*} [MeasureSpace X] (g : X → X) (k : ℝ) : Prop :=
  ∀ f : X → ℝ≥0∞, Measurable f → (∫⁻ x, f x) = ENNReal.ofReal |k| * ∫⁻ x, f (g x)

theorem affine_factor (b k : ℝ) (hk : k ≠ 0) : HasVolumeFactor (fun x => b+k*x) k := by
  intro f hf
  calc
    _ = ∫⁻ x, f (b+x) := (lintegral_add_left_eq_self f b).symm
    _ = ∫⁻ x, f (b+x) ∂(ENNReal.ofReal |k| • Measure.map (k*·) volume) := by
      rw [Real.smul_map_volume_mul_left hk]
    _ = _ := by rw [lintegral_smul_measure, lintegral_map (by fun_prop) (by fun_prop)]; rfl

theorem factor_prod {X Y : Type*} [MeasureSpace X] [MeasureSpace Y]
    [SFinite (volume : Measure Y)] {g : X → X} {h : X → Y → Y} {j k : ℝ}
    (hg : HasVolumeFactor g j) (hh : ∀ᵐ x, HasVolumeFactor (h x) k)
    (hm : Measurable (fun w : X × Y => (g w.1, h w.1 w.2))) :
    HasVolumeFactor (fun w : X × Y => (g w.1,h w.1 w.2)) (j*k) := by
  intro f hf
  rw [Measure.volume_eq_prod, lintegral_prod _ hf.aemeasurable,
    lintegral_prod (fun x => f (g x.1,h x.1 x.2)) (hf.comp hm).aemeasurable]
  rw [hg _ hf.lintegral_prod_right']
  have he : (∫⁻ x, ∫⁻ y, f (g x,y)) =
      ∫⁻ x, ENNReal.ofReal |k| * ∫⁻ y, f (g x,h x y) := by
    apply lintegral_congr_ae
    filter_upwards [hh] with x hx
    exact hx _ (hf.comp (measurable_const.prodMk measurable_id))
  rw [he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_mul,
    ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

def slopeMatrix (a : Triple) (t d p q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(1-p)/a 0, q^3*(t+d)/(d*a 0), q^3/(d*a 0);
      1/a 1, 0, 0;
      -p/a 2, -q^3*t/(d*a 2), -q^3/(d*a 2)]

theorem slope_det (a : Triple) (t d p q : ℝ) (ha : ∀ i, a i ≠ 0) (hd : d ≠ 0) :
    (slopeMatrix a t d p q).det = q^6/(a 0*a 1*a 2*d) := by
  simp [slopeMatrix, Matrix.det_fin_three]
  field_simp [ha,hd]; ring

def sMap (q : ℝ) (a : Triple) (t d p : ℝ) (v : Triple) : Triple :=
  ![leftJump t d p (v 0) (q^3*v 1) (q^3*v 2) / a 0, v 0 / a 1,
    rightJump t d p (v 0) (q^3*v 1) (q^3*v 2) / a 2]

theorem slope_factor (a : Triple) (t d p q : ℝ) (ha : ∀ i, a i ≠ 0) (hd : d ≠ 0) (hq : q ≠ 0) :
    HasVolumeFactor (sMap q a t d p) (q^6/(a 0*a 1*a 2*d)) := by
  let M := slopeMatrix a t d p q
  have hdet := slope_det a t d p q ha hd
  have hn : M.det ≠ 0 := by dsimp [M]; rw [hdet]; exact div_ne_zero (pow_ne_zero _ hq) (by aesop)
  have he : sMap q a t d p = (Matrix.toLin' M : Triple → Triple) := by
    funext v i
    change _ = (M.mulVec v) i
    fin_cases i <;> simp [sMap,M,slopeMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      leftJump,rightJump] <;> field_simp [ha,hd] <;> ring
  rw [he, ← hdet]
  intro f hf
  rw [← lintegral_map hf (M.toLin'.continuous_of_finiteDimensional.measurable),
    Real.map_matrix_volume_pi_eq_smul_volume_pi hn,lintegral_smul_measure]
  change _ = _ * (ENNReal.ofReal _ * _)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hn]
  simp

def pMap (q : ℝ) (a : Triple) (t d : ℝ) (w : ℝ × Triple) :=
  (-a 1*(t+w.1*d), sMap q a t d w.1 w.2)
def dMap (q : ℝ) (a : Triple) (t : ℝ) (w : ℝ × ℝ × Triple) :=
  (-a 2*(t+q^2*w.1), pMap q a t (q^2*w.1) w.2)
def tMap (q : ℝ) (a : Triple) (w : ℝ × ℝ × ℝ × Triple) :=
  (-a 0*w.1, dMap q a w.1 w.2)
def cMap (q : ℝ) (a : Triple) (w : ℝ × ℝ × ℝ × ℝ × Triple) :=
  (q^3*w.1, tMap q a w.2)
def scaledChart (q : ℝ) (w : Param) : Param := (w.1,cMap q w.1 w.2)

private theorem p_factor (q : ℝ) (a : Triple) (t d : ℝ) (ha : ∀ i, a i ≠ 0) (hd : d ≠ 0)
    (hq : q ≠ 0) : HasVolumeFactor (pMap q a t d) (-q^6/(a 0*a 2)) := by
  have h := affine_factor (-a 1*t) (-a 1*d) (by simp [ha,hd])
  have he : (fun x : ℝ => -a 1*t + -a 1*d*x) = (fun x => -a 1*(t+x*d)) := by funext x; ring
  rw [he] at h
  convert factor_prod h (Filter.Eventually.of_forall (fun p => slope_factor a t d p q ha hd hq))
    (by unfold sMap leftJump rightJump leftJump; fun_prop) using 1
  · rfl
  · field_simp [ha,hd]

private theorem d_factor (q : ℝ) (a : Triple) (t : ℝ) (ha : ∀ i, a i ≠ 0) (hq : q ≠ 0) :
    HasVolumeFactor (dMap q a t) (q^8/a 0) := by
  have h := affine_factor (-a 2*t) (-a 2*q^2) (by simp [ha,hq])
  have he : (fun x : ℝ => -a 2*t + -a 2*q^2*x) = (fun x => -a 2*(t+q^2*x)) := by funext x; ring
  rw [he] at h
  have hh : ∀ᵐ D : ℝ, HasVolumeFactor (pMap q a t (q^2*D)) (-q^6/(a 0*a 2)) := by
    filter_upwards [volume.ae_ne (0:ℝ)] with D hD
    exact p_factor q a t _ ha (mul_ne_zero (pow_ne_zero _ hq) hD) hq
  convert factor_prod h hh (by unfold pMap sMap leftJump rightJump leftJump; fun_prop) using 1
  · rfl
  · field_simp [ha]

private theorem t_factor (q : ℝ) (a : Triple) (ha : ∀ i, a i ≠ 0) (hq : q ≠ 0) :
    HasVolumeFactor (tMap q a) (-q^8) := by
  have h := affine_factor 0 (-a 0) (neg_ne_zero.mpr (ha 0))
  simp only [zero_add] at h
  convert factor_prod h (Filter.Eventually.of_forall (fun t => d_factor q a t ha hq))
    (by unfold dMap pMap sMap leftJump rightJump leftJump; fun_prop) using 1
  · rfl
  · field_simp [ha]

private theorem c_factor (q : ℝ) (a : Triple) (ha : ∀ i, a i ≠ 0) (hq : q ≠ 0) :
    HasVolumeFactor (cMap q a) (-q^11) := by
  have h := affine_factor 0 (q^3) (pow_ne_zero _ hq)
  simp only [zero_add] at h
  convert factor_prod h (Filter.Eventually.of_forall (fun _ : ℝ => t_factor q a ha hq))
    (by unfold tMap dMap pMap sMap leftJump rightJump leftJump; fun_prop) using 1
  · rfl
  · ring

theorem scaledChart_factor (q : ℝ) (hq : 0 < q) : HasVolumeFactor (scaledChart q) (q^11) := by
  have hi : HasVolumeFactor (id : Triple → Triple) (-1) := by intro f hf; simp
  have h : ∀ᵐ a : Triple, ∀ i, a i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin 3 => (volume : Measure ℝ)) i).ae
      (volume.ae_ne 0)
  convert factor_prod hi (h.mono (fun a ha => c_factor q a ha hq.ne'))
    (by unfold cMap tMap dMap pMap sMap leftJump rightJump leftJump; fun_prop) using 1
  · rfl
  · ring

end O71
