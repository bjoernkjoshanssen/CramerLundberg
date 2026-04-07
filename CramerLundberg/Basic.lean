import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Gamma

/-!

# Cramér-Lundberg distribution

Main result:
`first_loss_is_ruinous' (r s : ℝ) (hs : 0 < s) (hr : 0 < r) :`
`(Measure.prod (expMeasure r) (expMeasure s)) {x | x.1 ≤ x.2}`
    `= some ⟨r / (r + s), by field_simp;linarith⟩`
This is mostly hand-coded except that some integrability lemmas were
proved by Aristotle.
-/


open ProbabilityTheory MeasureTheory
open scoped BigOperators Real Nat Pointwise

lemma h₀ (z) : ∫ (a : ℝ) in Set.Ici 0, z * Real.exp (-(z * a))
            =  ∫ (a : ℝ), exponentialPDFReal z a := by
        unfold exponentialPDFReal
          gammaPDFReal
        generalize Real.exp = f
        have (g : ℝ → ℝ) :
          ∫ (a : ℝ) in Set.Ici 0, g a = ∫ (a : ℝ), if 0 ≤ a then g a else 0 := by
          rw [← integral_indicator]
          · exact Real.ext_cauchy rfl
          · simp
        simp [this]

lemma g₀ (s r x : ℝ) : s * Real.exp (-(s * x)) * Real.exp (-(r * x))
                     = s * Real.exp (-((s+r) * x)) := by
  rw [mul_assoc]
  congr
  rw [← Real.exp_add]
  congr
  linarith

-- We need five "obvious" lemmas about measurability and integrability.
lemma ae {r s : ℝ} (x : ℝ) :
 AEStronglyMeasurable (fun y ↦ if x ≤ y then
 exponentialPDFReal r x * exponentialPDFReal s y else 0) volume
:= by
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  refine Measurable.aemeasurable ?_
  refine Measurable.ite ?_ ?_ ?_
  · apply measurableSet_Ici
  · refine Measurable.mul ?_ ?_
    · exact measurable_const
    · exact measurable_exponentialPDFReal s
  simp

lemma h₂ (z : ℝ) (hz : 0 < z) :
    ∫ (y : ℝ), exponentialPDFReal z y = 1 := by
  have := @lintegral_exponentialPDF_eq_one z hz
  have h₁ : (1 : ℝ) = (1 : ENNReal).toReal := rfl
  rw [h₁]
  rw [← this]
  refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
  · rw [Filter.EventuallyLE, Filter.Eventually]
    exact Filter.univ_mem' <| exponentialPDFReal_nonneg hz
  unfold exponentialPDFReal
    gammaPDFReal
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  refine Measurable.aemeasurable ?_
  refine Measurable.ite measurableSet_Ici ?_ measurable_const
  · exact Measurable.mul measurable_const <|Measurable.exp
      <| Measurable.neg <| measurable_const_mul z

lemma first_loss_is_ruinous {r s : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∫ (y : ℝ) in Set.Ici 0, (∫ (x : ℝ) in Set.Iic y,
      exponentialPDFReal s y *
      exponentialPDFReal r x) = r / (r + s) := by
  simp_rw [integral_const_mul]
  have h₁ := @cdf_expMeasure_eq_integral r hr
  simp_rw [← h₁]
  simp_rw [@cdf_expMeasure_eq r hr]
  unfold exponentialPDFReal gammaPDFReal
  suffices (∫ (y : ℝ) in Set.Ici 0,
    if 0 ≤ y then s * Real.exp (-(s * y)) * (1 - Real.exp (-(r * y))) else 0) =
    r / (r + s) by
    rw [← this]
    congr
    ext y
    simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one, mul_ite,
      ite_mul, zero_mul, mul_zero, ite_eq_left_iff, not_le, right_eq_ite_iff, zero_eq_mul,
      mul_eq_zero, Real.exp_ne_zero, or_false]
    intro h₀ h₁
    linarith
  suffices (∫ (y : ℝ) in Set.Ici 0,
    s * Real.exp (-(s * y)) * (1 - Real.exp (-(r * y)))) = r / (r + s) by
    rw [← this]
    apply integral_congr_ae
    refine Set.EqOn.aeEq_restrict ?_ ?_
    · intro x hx
      simp only [ite_eq_left_iff, not_le, zero_eq_mul, mul_eq_zero, Real.exp_ne_zero, or_false]
      intro hx₀
      simp at hx
      linarith
    · simp
  simp_rw [mul_sub]
  simp only [mul_one]
  rw [integral_sub]
  · have : ∫ (a : ℝ) in Set.Ici 0, s * Real.exp (-(s * a)) = 1 := by
      rw [h₀]
      exact EReal.coe_eq_one.mp (congrArg Real.toEReal (h₂ s hs))
    rw [this]
    simp_rw [g₀]
    rw [integral_const_mul]
    have :          ∫ (x : ℝ) in Set.Ici 0, Real.exp (-((s + r) * x))
      = (1/(s+r)) * ∫ (x : ℝ) in Set.Ici 0, (s+r) * Real.exp (-((s + r) * x)) := by
        rw [integral_const_mul]
        field_simp
    rw [this]
    rw [h₀, h₂]
    · field_simp
      linarith
    · linarith
  · refine integrable_of_integral_eq_one ?_
    rw [h₀]
    rw [h₂]
    exact hs
  · simp_rw [g₀]
    have : (fun y ↦ s * Real.exp (-((s + r) * y)))
         = (fun _ => s / (s + r)) * (fun y ↦ (s + r) * Real.exp (-((s + r) * y))) := by
      ext y
      simp
      field_simp
    rw [this]
    refine Integrable.const_mul' ?_ _
    refine integrable_of_integral_eq_one ?_
    rw [h₀]
    rw [h₂]
    linarith

-- example (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
--     Measure.pi ![expMeasure r, expMeasure s]
--     {v | v 0 ≤ v 1} = some ⟨r / (r + s), by field_simp;linarith⟩ := by
--   -- rw [measure_eq_integral]
--   have := @first_loss_is_ruinous r s hs hr
--   simp_rw [← this]
--   simp
--   have (q : ℝ) : expMeasure q = volume.withDensity (exponentialPDF q) := by
--     rfl
--   repeat rw [this]
--   rw [Measure.withDensity]
--   unfold exponentialPDF
--   -- have := @integral_indicator

--   -- have := @lintegral_withDensity_eq_lintegral_mul
--   zorry

lemma exp_nonneg {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (x y : ℝ) :
0 ≤ if x ≤ y then exponentialPDFReal r x * exponentialPDFReal s y else 0
:= by
              split_ifs with g₀
              · apply mul_nonneg
                · exact exponentialPDFReal_nonneg hr x
                · exact exponentialPDFReal_nonneg hs y
              · simp

lemma measExp₁ (r : ℝ) : Measurable fun (a : ℝ × ℝ) ↦ exponentialPDFReal r a.1 := by
            refine Measurable.ite ?_ ?_ ?_
            · simp only [measurableSet_setOf]
              refine Measurable.le' measurable_const measurable_fst
            · refine Measurable.mul ?_ ?_
              · refine Measurable.mul measurable_const <| Measurable.pow_const measurable_fst _
              · refine Measurable.exp <| Measurable.neg
                  <| Measurable.mul measurable_const measurable_fst
            simp

lemma measExp₂ (r : ℝ) : Measurable fun (a : ℝ × ℝ) ↦ exponentialPDFReal r a.2 := by
  refine Measurable.ite ?_ ?_ ?_
  · simp only [measurableSet_setOf]
    refine Measurable.le' measurable_const measurable_snd
  · refine Measurable.mul ?_ ?_
    · refine Measurable.mul measurable_const <| Measurable.pow_const measurable_snd _
    · refine Measurable.exp <| Measurable.neg <| Measurable.mul measurable_const measurable_snd
  simp

lemma ae' {r s : ℝ} :
AEMeasurable (fun a ↦ {x | x.1 ≤ x.2}.indicator
  (fun a ↦ exponentialPDF r a.1 * exponentialPDF s a.2) a)
  (volume.prod volume) := by
      refine (aemeasurable_indicator_iff ?_).mpr ?_
      · simp only [measurableSet_setOf]
        exact measurable_le
      · refine Measurable.aemeasurable ?_
        refine measurable_coe_nnreal_ennreal_iff.mpr ?_
        refine Measurable.mul ?_ ?_
        all_goals
            refine Measurable.real_toNNReal ?_
        · apply measExp₁
        · apply measExp₂

lemma exponentialPDFReal_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (exponentialPDFReal r) volume := by
      apply MeasureTheory.Integrable.mono' _ _ _;
      · apply fun x => if x ≥ 0 then r * Real.exp ( -r * x ) else 0;
      · -- The integral of the exponential function is convergent.
        have h_exp : ∫ x in Set.Ici 0, Real.exp (-r * x) = 1 / r := by
          rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ] ;
          have := integral_exp_neg_mul_rpow zero_lt_one hr
          norm_num [ Real.rpow_neg_one ] at * ; aesop;
        apply MeasureTheory.integrable_indicator_iff ( measurableSet_Ici ) |>.2 _;
        exact MeasureTheory.Integrable.const_mul
          (( by contrapose! h_exp; rw [ MeasureTheory.integral_undef h_exp ]
                norm_num; positivity ) ) _;
      · exact Measurable.aestronglyMeasurable (Measurable.ite ( measurableSet_Ici )
          (by measurability) (by measurability ) );
      · simp only [exponentialPDFReal, Real.norm_eq_abs, ge_iff_le, neg_mul];
        filter_upwards [ ] with x
        split_ifs
        · simp_all only [gammaPDFReal, ↓reduceIte, Real.rpow_one, Real.Gamma_one, div_one, sub_self,
            Real.rpow_zero, mul_one, abs_mul, Real.abs_exp];
          rw [ abs_of_pos hr ]
        · simp_all [ gammaPDFReal ];

lemma integ {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Integrable (fun (a : ℝ × ℝ) ↦ if a.1 ≤ a.2 then
      exponentialPDFReal r a.1 * exponentialPDFReal s a.2 else 0) (volume.prod volume) := by
        apply MeasureTheory.Integrable.indicator _ _;
        · exact MeasureTheory.Integrable.mul_prod ( exponentialPDFReal_integrable hr )
            ( exponentialPDFReal_integrable hs );
        · exact measurableSet_le measurable_fst measurable_snd

lemma integ₀ {r s : ℝ} (hs : 0 < s) (x : ℝ) :
 Integrable (fun (y : ℝ) ↦ if x ≤ y then
 exponentialPDFReal r x * exponentialPDFReal s y else 0) volume := by
        have := @MeasureTheory.Integrable.indicator ℝ ℝ Real.measurableSpace
          {y | x ≤ y} volume _ _
        apply this
        · generalize exponentialPDFReal r x = α
          apply Integrable.const_mul
          exact exponentialPDFReal_integrable hs
        · apply measurableSet_le
          · simp only [measurable_const]
          · exact measurable_id'

open MeasureTheory ProbabilityTheory MeasureTheory.Measure


theorem integrable_exponential_joint (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    Integrable (fun x ↦ ∫ (y : ℝ), if x ≤ y then
    exponentialPDFReal r x * exponentialPDFReal s y else 0) volume := by
  -- The inner integral can be computed explicitly.
  have h_inner : ∀ x, ∫ y, (if x ≤ y then
  (exponentialPDFReal r x) * (exponentialPDFReal s y) else 0)
    = (exponentialPDFReal r x) * (if 0 ≤ x then Real.exp (-s * x) else 1) := by
    intro x
    by_cases hx : 0 ≤ x;
    · -- For $x \geq 0$, we can simplify the integral.
      have h_simp : ∫ y in Set.Ici x, exponentialPDFReal s y = Real.exp (-s * x) := by
        have h_inner : ∫ y in Set.Ici x, s * Real.exp (-s * y) = Real.exp (-s * x) := by
          have := integral_exp_neg_mul_rpow zero_lt_one hs;
          rw [ MeasureTheory.integral_Ici_eq_integral_Ioi ]
          rw [ MeasureTheory.integral_const_mul ]
          rw [ show ( ∫ y in Set.Ioi x, Real.exp ( -s * y ) )
            = ( ∫ y in Set.Ioi 0, Real.exp ( -s * ( y + x ) ) ) by
              rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ),
              ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ] ;
              rw [ ← MeasureTheory.integral_add_right_eq_self _ x ] ; congr; ext y;
              rw [ Set.indicator_apply, Set.indicator_apply ] ; aesop ] ;
              simp_all +decide only [Real.rpow_one, neg_mul, div_one, Real.rpow_neg_one, ne_eq,
                one_ne_zero, not_false_eq_true, div_self, mul_add, Real.exp_add];
          rw [ MeasureTheory.integral_mul_const, this ] ; norm_num [ hs.ne' ];
        convert h_inner using 1;
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun y hy => ?_
        simp [exponentialPDFReal];
        simp +decide [ gammaPDFReal];
        grind;
      simp_all +decide only [measurableSet_Ici, ← integral_indicator, Set.indicator_apply,
        Set.mem_Ici, neg_mul, ↓reduceIte];
      rw [ ← h_simp, ← MeasureTheory.integral_const_mul ] ; congr ; ext ; split_ifs <;> ring;
    · rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ]
        <;> norm_num [ hx, exponentialPDFReal ];
      · change ∫ y in Set.Ici x, gammaPDFReal 1 r x * gammaPDFReal 1 s y = gammaPDFReal 1 r x;
        · rw [ MeasureTheory.integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi ];
          norm_num [ gammaPDFReal ];
          grind;
      · norm_num;
      · norm_num [ Filter.EventuallyEq, Set.indicator ];
  simp_all +decide only [exponentialPDFReal, mul_comm, mul_neg, Real.exp_neg, mul_ite, one_mul];
  have h_integrable : MeasureTheory.Integrable (fun x => (if 0 ≤ x then Real.exp (-r * x) else 0) *
    (if 0 ≤ x then Real.exp (-s * x) else 1)) MeasureTheory.volume := by
    have h_integrable : MeasureTheory.IntegrableOn
      (fun x => Real.exp (-(r + s) * x)) (Set.Ici 0) := by
      have := ( exp_neg_integrableOn_Ioi 0 ( by linarith : 0 < r + s ) );
      rwa [ MeasureTheory.IntegrableOn,
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici ] at *;
    rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ici ) ] at *;
    convert h_integrable using 1 ; ext x ; split_ifs <;> simp_all +decide [ ← Real.exp_add ] ; ring;
  convert h_integrable.const_mul ( r : ℝ ) using 2
  norm_num [ Real.exp_neg, Real.exp_ne_zero, hr.ne', hs.ne', gammaPDFReal ] ; ring_nf

lemma first_loss_is_ruinous' (r s : ℝ) (hs : 0 < s) (hr : 0 < r) :
    (Measure.prod (expMeasure r) (expMeasure s)) {x | x.1 ≤ x.2}
    = some ⟨r / (r + s), by field_simp;linarith⟩ := by
  have (q : ℝ) : expMeasure q = volume.withDensity (exponentialPDF q) := by
    rfl
  have h₀ := @prod_withDensity ℝ _ volume ℝ _ volume
    _ (exponentialPDF r) (exponentialPDF s)
    (Measurable.ennreal_ofReal <| measurable_exponentialPDFReal _)
    (Measurable.ennreal_ofReal <| measurable_exponentialPDFReal _)
  have :  (volume.withDensity (exponentialPDF r)).prod (volume.withDensity (exponentialPDF s))
    = (Measure.prod (expMeasure r) (expMeasure s)) := by
      exact Measure.ext_iff.mpr fun s_1 ↦ congrFun rfl
  rw [← this]
  rw [h₀]
  have := @first_loss_is_ruinous r s hs hr
  simp_rw [← this]
  rw [withDensity_apply]
  · have h₀ := @lintegral_indicator
      (ℝ × ℝ) Prod.instMeasurableSpace
      volume {x | x.1 ≤ x.2}
      measurableSet_le'
      (fun a => exponentialPDF r a.1 * exponentialPDF s a.2)
    symm at this
    have h₁ : (@Measure.prod ℝ ℝ _ _ volume volume : Measure (ℝ × ℝ))
         = (@volume (ℝ × ℝ) Measure.prod.measureSpace : Measure (ℝ × ℝ)) := by
        exact Eq.symm (Measure.volume_eq_prod ℝ ℝ)
    rw [h₁]
    rw [← h₀]
    have h₂ := @lintegral_prod (α := ℝ) (β := ℝ) (μ := volume) (ν := volume)
      (f := fun a => {x | x.1 ≤ x.2}.indicator
        (fun a ↦ exponentialPDF r a.1 * exponentialPDF s a.2) a)
    have h₃ : (@Measure.prod ℝ ℝ _ _ volume volume : Measure (ℝ × ℝ))
         = (@volume (ℝ × ℝ) Measure.prod.measureSpace : Measure (ℝ × ℝ)) := by
        exact Eq.symm (Measure.volume_eq_prod ℝ ℝ)
    rw [← h₃]
    rw [h₂]
    · unfold Set.indicator
      simp only [Set.mem_setOf_eq, ENNReal.some_eq_coe]
      -- looks good, integrate over all x,y with x ≤ y
      unfold exponentialPDF
      have H₀ (x y : ℝ) :
      (if x ≤ y then ENNReal.ofReal (exponentialPDFReal r x)
                   * ENNReal.ofReal (exponentialPDFReal s y) else 0)
      =
      ENNReal.ofReal ( if x ≤ y then (exponentialPDFReal r x)
                                   * (exponentialPDFReal s y) else 0) := by
        split_ifs with g₀
        · refine Eq.symm (ENNReal.ofReal_mul ?_)
          exact exponentialPDFReal_nonneg hr x
        · exact Eq.symm ENNReal.ofReal_zero
      simp_rw [H₀]
      have (x : ℝ) :
        ∫⁻ (y : ℝ), ENNReal.ofReal (if x ≤ y then exponentialPDFReal r x
        * exponentialPDFReal s y else 0)
       = ENNReal.ofReal (∫ (y : ℝ), if x ≤ y then exponentialPDFReal r x
       * exponentialPDFReal s y else 0 ∂volume) := by
          -- have := @lintegral_prod
          have := @ofReal_integral_eq_lintegral_ofReal
            (α := ℝ) (m := Real.measurableSpace)
            (μ := volume)
            (f := fun y => (if x ≤ y then exponentialPDFReal r x * exponentialPDFReal s y else 0))
          rw [← this]
          · apply integ₀ hs
          · simp only [Filter.EventuallyLE, Filter.Eventually, Pi.zero_apply]
            have : {x_1 | 0 ≤ if x ≤ x_1 then
              exponentialPDFReal r x * exponentialPDFReal s x_1 else 0}
              = Set.univ := by
              ext y
              simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
              apply exp_nonneg hr hs
            rw [this]
            exact Filter.univ_mem
      simp_rw [this]
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · have (x : ℝ) (hx : 0 ≤ x) :
          ENNReal.ofNNReal (⟨x,hx⟩ : NNReal) =
          ENNReal.ofReal x := by
            exact Eq.symm (ENNReal.ofReal_eq_coe_nnreal hx)
        rw [this]
        apply congrArg -- yes!
        have hswap: (∫ (x : ℝ) (y : ℝ), if x ≤ y then
                exponentialPDFReal r x * exponentialPDFReal s y else 0)
                =  (∫ (y : ℝ) (x : ℝ), if x ≤ y then
                exponentialPDFReal r x * exponentialPDFReal s y else 0) := by
          apply integral_integral_swap
          -- certainly true...
          unfold Function.uncurry
          apply integ hr hs
        rw [← integral_indicator]
        · unfold Set.indicator
          simp only [Set.mem_Ici]
          rw [hswap]
          congr
          ext x
          split_ifs with g₀
          · rw [← integral_indicator]
            · unfold Set.Iic Set.indicator
              congr
              ext z
              rw [mul_comm]
              simp
            · simp
          · simp at g₀
            have : exponentialPDFReal s x = 0 := by
              unfold exponentialPDFReal gammaPDFReal
              split_ifs with g₁
              · linarith
              · rfl
            rw [this]
            simp
        · simp
      · apply integrable_exponential_joint _ _ hr hs
      · simp only [Filter.EventuallyLE, Filter.Eventually, Pi.zero_apply]
        refine Filter.univ_mem' ?_
        intro a
        simp only [Set.mem_setOf_eq]
        have : 0 = ∫ (y : ℝ), (0:ℝ) := by simp
        nth_rw 1 [this]
        apply integral_mono
        · apply integrable_zero
        · apply integ₀ hs
        · intro x
          apply exp_nonneg hr hs
    · exact instSFiniteOfSigmaFinite
    · apply ae'
  · exact measurableSet_le'

-- lemma second_loss_is_ruinous (r s a : ℝ) (hs : 0 < s) (hr : 0 < r) :
--     ∫ (x₀ : ℝ) in Set.Ici 0,
--       exponentialPDFReal r x₀ *
--     ∫ (x₁ : ℝ) in Set.Ici 0,
--       exponentialPDFReal r x₁ *
--     ∫ (y₀ : ℝ) in Set.Ici 0,
--       exponentialPDFReal s y₀ *
--     ∫ (y₁ : ℝ) in Set.Ici (max (x₀ + x₁ - y₀) 0),
--       exponentialPDFReal s y₁
--       = a := by

--   zorry
