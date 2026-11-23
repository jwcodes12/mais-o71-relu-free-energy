import Scaling

noncomputable section
namespace O71
set_option maxHeartbeats 500000

private theorem mass_lower (u v : ℝ) : u^2 + v^2 ≤ 2 * mass u v := by
  unfold mass; nlinarith [sq_nonneg (u+v)]

/-- Uniform bounds for the three macroscopic coordinates and for the squared tent amplitude.
The normalized loss inequality allows constants independent of the knot ratio and total gap. -/
theorem coercive (q c t D p z S B : ℝ) (hD : 0 < D)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (ht : -(1/2) ≤ t) (hr : t+q^2*D ≤ 1/2)
    (hE : scaledEnergy q c t D p z S B ≤ 1) :
    |c| ≤ 4 ∧ |S| ≤ 32 ∧ |B| ≤ 44 ∧ (z*p*(1-p))^2 * D^3 ≤ 256 := by
  let d := q^2*D
  let n := c+B+S*(t+d)
  let k := c+B+S
  let m := q*(c+p*(B+S*(t+d)))-z*p*(1-p)*D
  change ((1+t)*3*c^2 + p*D*mass (q*c) m + (1-p)*D*mass m (q*n) +
    (1-(t+d))*mass n k)/12 ≤ 1 at hE
  change t+d ≤ 1/2 at hr
  have hn (u v : ℝ) : 0 ≤ mass u v := by nlinarith [mass_lower u v,sq_nonneg u,sq_nonneg v]
  have hi₁ : p*D*m^2 ≤ 2*(p*D*mass (q*c) m) := by
    have hm : m^2 ≤ 2*mass (q*c) m := by linarith [mass_lower (q*c) m, sq_nonneg (q*c)]
    nlinarith only [mul_le_mul_of_nonneg_left hm (mul_nonneg hp hD.le)]
  have hi₂ : (1-p)*D*m^2 ≤ 2*((1-p)*D*mass m (q*n)) := by
    have hm : m^2 ≤ 2*mass m (q*n) := by linarith [mass_lower m (q*n), sq_nonneg (q*n)]
    nlinarith only [mul_le_mul_of_nonneg_left hm (mul_nonneg (sub_nonneg.mpr hp') hD.le)]
  have hleft : 3*c^2/2 ≤ (1+t)*3*c^2 := by nlinarith only [mul_nonneg (show 0 ≤ 1/2+t by linarith) (sq_nonneg c)]
  have hright : (n^2+k^2)/4 ≤ (1-(t+d))*mass n k := by
    nlinarith only [mass_lower n k,mul_nonneg (show 0 ≤ 1/2-(t+d) by linarith) (hn n k)]
  have htotal : 3*c^2/2+D*m^2/2+(n^2+k^2)/4 ≤ 12 := by nlinarith only [hE,hi₁,hi₂,hleft,hright]
  have hmD := mul_nonneg hD.le (sq_nonneg m)
  have hc : |c| ≤ 4 := by nlinarith only [htotal,hmD,sq_nonneg n,sq_nonneg k,sq_abs c,abs_nonneg c]
  have hn' : |n| ≤ 8 := by nlinarith only [htotal,hmD,sq_nonneg c,sq_nonneg k,sq_abs n,abs_nonneg n]
  have hk : |k| ≤ 8 := by nlinarith only [htotal,hmD,sq_nonneg c,sq_nonneg n,sq_abs k,abs_nonneg k]
  have hs : S*(1-(t+d)) = k-n := by dsimp [k,n]; ring
  have hs' := abs_sub k n
  rw [← hs,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-(t+d))] at hs'
  have hS : |S| ≤ 32 := by
    nlinarith only [hs',hk,hn',mul_nonneg (abs_nonneg S) (show 0 ≤ 1/2-(t+d) by linarith)]
  have hB : |B| ≤ 44 := by
    rw [show B = (k-c)-S by dsimp [k]; ring]
    grw [abs_sub,abs_sub,hk,hc,hS]; norm_num
  let u := (1-p)*c+p*n
  have hu : |u| ≤ 8 := calc
    _ ≤ |(1-p)*c| + |p*n| := abs_add_le ..
    _ ≤ (1-p)*4+p*8 := by
      rw [abs_mul,abs_mul,abs_of_nonneg hp,abs_of_nonneg (sub_nonneg.mpr hp')]
      gcongr
    _ ≤ 8 := by linarith
  have hu₂ : u^2 ≤ 64 := by nlinarith only [sq_abs u,abs_nonneg u,hu]
  have hd : 0 ≤ d := mul_nonneg (sq_nonneg q) hD.le
  have hd' : d ≤ 1 := by linarith
  have huD : D*(q*u)^2 ≤ 64 := by
    calc _ = d*u^2 := by dsimp [d]; ring
         _ ≤ 1*64 := mul_le_mul hd' hu₂ (sq_nonneg _) zero_le_one
         _ = _ := by norm_num
  have H : q*u-m = z*p*(1-p)*D := by dsimp [u,m,n]; ring
  have H' : (q*u-m)^2 ≤ 2*((q*u)^2+m^2) := by nlinarith [sq_nonneg (q*u+m)]
  refine ⟨hc,hS,hB,?_⟩
  rw [H] at H'
  nlinarith only [mul_le_mul_of_nonneg_left H' hD.le,huD,htotal,sq_nonneg c,sq_nonneg k,sq_nonneg n]

end O71
