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


lemma integral_exponentialPDFReal_eq (z) :
    ∫ a, exponentialPDFReal z a =
    ∫ a in Set.Ici 0, z * Real.exp (-(z * a)) := by
  rw [← integral_indicator]
  · simp [exponentialPDFReal, gammaPDFReal]
    rfl
  · simp

lemma Real.exp_assoc_add (s r x : ℝ) :
    s * Real.exp (-(s * x)) * Real.exp (-(r * x)) =
    s * Real.exp (-((s+r) * x)) := by
  rw [mul_assoc]
  congr
  rw [← Real.exp_add]
  congr
  linarith

-- We need five "obvious" lemmas about measurability and integrability.
lemma ae {r s : ℝ} (x : ℝ) :
    AEStronglyMeasurable (fun y ↦ if x ≤ y then
    exponentialPDFReal r x * exponentialPDFReal s y else 0) volume := by
  refine aestronglyMeasurable_iff_aemeasurable.mpr ?_
  refine Measurable.aemeasurable ?_
  refine Measurable.ite ?_ ?_ ?_
  · apply measurableSet_Ici
  · refine Measurable.mul measurable_const <| measurable_exponentialPDFReal s
  simp

lemma integral_exponentialPDFReal_eq_one (z : ℝ) (hz : 0 < z) :
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
      rw [← integral_exponentialPDFReal_eq]
      exact EReal.coe_eq_one.mp (congrArg Real.toEReal
        (integral_exponentialPDFReal_eq_one s hs))
    rw [this]
    simp_rw [Real.exp_assoc_add]
    rw [integral_const_mul]
    have :          ∫ (x : ℝ) in Set.Ici 0, Real.exp (-((s + r) * x))
      = (1/(s+r)) * ∫ (x : ℝ) in Set.Ici 0, (s+r) * Real.exp (-((s + r) * x)) := by
        rw [integral_const_mul]
        field_simp
    rw [this]
    rw [← integral_exponentialPDFReal_eq,
      integral_exponentialPDFReal_eq_one]
    · field_simp
      linarith
    · linarith
  · refine integrable_of_integral_eq_one ?_
    rw [← integral_exponentialPDFReal_eq]
    rw [integral_exponentialPDFReal_eq_one]
    exact hs
  · simp_rw [Real.exp_assoc_add]
    have : (fun y ↦ s * Real.exp (-((s + r) * y)))
         = (fun _ => s / (s + r)) * (fun y ↦ (s + r) * Real.exp (-((s + r) * y))) := by
      ext y
      simp
      field_simp
    rw [this]
    refine Integrable.const_mul' ?_ _
    refine integrable_of_integral_eq_one ?_
    rw [← integral_exponentialPDFReal_eq]
    rw [integral_exponentialPDFReal_eq_one]
    linarith

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

/-- Probably the assumption of σ-finiteness is not needed,
but that's fine. -/
lemma sigmaFiniteMeasure_pi_prod (μ ν : Measure ℝ)
  [SigmaFinite μ] [SigmaFinite ν] :
    Measure.pi ![μ, ν] {v | v 0 ≤ v 1} =
    Measure.prod μ ν {v | v.fst ≤ v.snd} := by
  have h := (@MeasureTheory.measurePreserving_finTwoArrow_vec
    ℝ Real.measurableSpace μ ν _ _).map_eq
  have h₁ : Measure.map (finTwoArrowEquiv ℝ)
    (Measure.pi ![μ, ν]) = Measure.prod μ ν := by
    rw [← h]
    simp
  rw [← h₁]
  symm
  rw [Measure.map_apply]
  · simp
  · refine Measurable.prodMk ?_ ?_
    all_goals exact measurable_pi_apply _
  · simp only [measurableSet_setOf];exact measurable_le

lemma expMeasure_pi_prod (r s : ℝ) :
    Measure.pi ![expMeasure r, expMeasure s] {v | v 0 ≤ v 1} =
    Measure.prod (expMeasure r) (expMeasure s) {v | v.fst ≤ v.snd} := by
  apply @sigmaFiniteMeasure_pi_prod (expMeasure r) (expMeasure s)
    (SigmaFinite.withDensity_of_ne_top' <| by simp [gammaPDF])
    (SigmaFinite.withDensity_of_ne_top' <| by simp [gammaPDF])

  -- rw [measure_eq_integral]
  -- have := @first_loss_is_ruinous r s hs hr
  -- simp_rw [← this]
  -- simp
  -- have (q : ℝ) : expMeasure q = volume.withDensity (exponentialPDF q) := by
  --   rfl
  -- repeat rw [this]
  -- rw [Measure.withDensity]
  -- unfold exponentialPDF
  -- -- have := @integral_indicator

  -- -- have := @lintegral_withDensity_eq_lintegral_mul
  -- zorry

lemma first_loss_is_ruinous'' (r s : ℝ) (hs : 0 < s) (hr : 0 < r) :
    (Measure.pi ![expMeasure r, expMeasure s]) {x | x 0 ≤ x 1}
    = some ⟨r / (r + s), by field_simp;linarith⟩ := by
    rw [expMeasure_pi_prod]
    exact first_loss_is_ruinous' r s hs hr


-- In the degenerate case `s=0`, the measure becomes 0.
lemma first_loss_is_ruinous_zero (r s : ℝ) (hs : s = 0)
  :
    (Measure.prod (expMeasure r) (expMeasure s)) {x | x.1 ≤ x.2}
    = 0 := by
  subst s
  unfold expMeasure gammaMeasure gammaPDF gammaPDFReal
  simp

-- In the degenerate case `r=0`, the measure becomes 0.
lemma first_loss_is_ruinous_zero' (r s : ℝ) (hr : r = 0) :
    (Measure.prod (expMeasure r) (expMeasure s)) {x | x.1 ≤ x.2}
    = 0 := by
  subst r
  unfold expMeasure gammaMeasure gammaPDF gammaPDFReal
  simp


def integralEquation (α β c : ℝ) (φ : ℝ → ℝ) :=
  ∀ u ≥ 0, φ u = ∫ t, exponentialPDFReal α t * ∫ x in Set.Iic (u + c * t),
    φ (u + c * t - x) * exponentialPDFReal β x

lemma integralEquaton_invariance (α β c d : ℝ) (φ : ℝ → ℝ) (h : integralEquation α β c φ)
    (hd : 0 < d)
    :
    integralEquation (α*d) (β*d) (c*d) (fun u => φ (u/d)) := by

    unfold integralEquation at *
    simp
    have hex (x γ : ℝ) : exponentialPDFReal (γ*d) x
        = (d) * exponentialPDFReal γ (x*d) := by
      unfold exponentialPDFReal gammaPDFReal
      simp
      split_ifs with g₀ g₁ g₂
      · ring_nf
      · exfalso;apply g₁;apply mul_nonneg <;> linarith
      · exfalso
        revert g₂
        simp at g₀ ⊢
        exact mul_neg_of_neg_of_pos g₀ hd
      · rfl
    intro u hu
    rw [h]
    repeat simp_rw [hex]
    have hii (t : ℝ) := @integral_indicator ℝ ℝ
        Real.measurableSpace _ _
        (fun x =>  φ ((u + c * d * t - x) / d) * (d * exponentialPDFReal β (x * d)))
        (Set.Iic (u+c*d*t)) volume (by simp)
    simp_rw [← hii]
    have hi := @integral_comp_mul_left ℝ _ _
    sorry
    -- have hh (x t : ℝ) :
    --     (u + c * d * t - x) / d
    --     =
    --     ((u + c * d * t) / d)
    --     -
    --     ((1/d) * (x))

    --     := by ring_nf
    -- simp_rw [hh]
    -- have (t : ℝ) := @integral_indicator ℝ ℝ
    --     Real.measurableSpace _ _
    --     (fun x => φ ((u + c * d * t) / d - 1 / d * x) * exponentialPDFReal (β * d) x)
    --     (Set.Iic (u+c*d*t))
    --     volume (by simp)
    --     -- (s := Set.Iic (u+c*d*t))
    --     -- (f := fun x => φ ((u + c * d * t) / d - 1 / d * x) * exponentialPDFReal (β * d) x)
    -- simp_rw [← this]
    -- conv =>
    -- right
    -- right
    -- change fun t ↦
    --     exponentialPDFReal (α * d) t *
    --         ∫ (x : ℝ),
    --         (Set.Iic (u + c * d * t)).indicator (fun x ↦ φ ((u + c * d * t) / d - 1 / d * x) * exponentialPDFReal (β * d) x)
    --             x -- just removing the ∂volume
    -- have hi := @integral_comp_mul_left ℝ _ _ (a := 1 / d)
    -- have hi (t : ℝ) := hi (
    --     (Set.Iic (u + c * d * t)).indicator
    --         (fun x ↦ φ ((u + c * d * t) / d - 1 / d * x)
    --             * exponentialPDFReal (β * d) x))
    -- simp at this
    -- have hyz (y z : ℝ) : |d| * y = |d| * z → y = z := by sorry
    -- apply hyz
    -- rw [← integral_const_mul]
    -- simp_rw [← mul_assoc]
    -- simp_rw [mul_comm (a := |d|) (b := exponentialPDFReal (α * d) _)]
    -- simp_rw [mul_assoc]
    -- have (a : ℝ) : (u + c * (d * a))
    --     = (u + c * d * a) := by sorry
    -- simp_rw [this]
    -- have : 1 / d = d⁻¹ := sorry
    -- rw [this]
    -- simp at hi
    -- simp_rw [← hi] -- Yes!
    -- specialize h (u/d) (by sorry)
    -- rw [h]

    sorry

lemma exists_solution (α β c : ℝ) :
    ∃ φ, integralEquation α β c φ := by
  use 0
  simp [integralEquation]

lemma exists_solution' (β c : ℝ) (φ : ℝ → ℝ) :
    integralEquation 0 β c φ → ∀ u ≥ 0, φ u = 0 := by
  unfold integralEquation exponentialPDFReal gammaPDFReal
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one, zero_mul,
    neg_zero, Real.exp_zero, ite_self, mul_ite, mul_zero, integral_zero]
  tauto

lemma exists_solution'' (α c : ℝ) (φ : ℝ → ℝ) :
    integralEquation α 0 c φ → ∀ u ≥ 0, φ u = 0 := by
  unfold integralEquation exponentialPDFReal gammaPDFReal
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one, zero_mul,
    neg_zero, Real.exp_zero, ite_self, mul_zero, integral_zero]
  tauto

/-- u = starting capital, φ u = nonruin probability,
c = income rate, α = loss rate, β = loss-amount-stop-rate
The equation for `φ` is from the end of
https://en.wikipedia.org/wiki/Ruin_theory#Classical_model
`hc` says that the income rate makes the game exactly evenly fair
as in Applied Math Seminar April 8, 2026.
-/
lemma too_fair (α β c : ℝ) (φ : ℝ → ℝ) (hα : α ≠ 0)
    (hβ : β ≠ 0)
    (h : φ = fun u => 1 - ((α * β) / c) * Real.exp (-(1 / β - α / c) * u))
    (hc : c = α * β) :
    integralEquation α β c φ := by
  subst c
  rw [h]
  have : α * β / (α * β) = 1 := by
    field_simp
  rw [this]
  have : (1 / β - α / (α * β)) = 0 := by
    field_simp
    linarith
  rw [this]
  simp [integralEquation]
open Real

lemma itemul
(x y z : ℝ)
: (if 0 ≤ x then y * z else 0) = y * if 0 ≤ x then z else 0 := by
    split_ifs  <;> simp

lemma ite_sub' (x y z : ℝ) :
    (if (0 ≤ x) then (y - z) else 0) =
    (if (0 ≤ x) then y else 0) -
    (if (0 ≤ x) then z else 0) := by
    split_ifs  <;> simp


lemma ite_ite (f : ℝ → ℝ) :
        (∫ a, if 0 ≤ a then (if 0 ≤ a then f a else 0) else 0)
        =
        (∫ a, (if 0 ≤ a then f a else 0))
        := by
        congr
        ext a
        simp only [ite_eq_left_iff, not_le, right_eq_ite_iff]
        intro h₀ h₁
        linarith


lemma integrableExp (δ : ℝ) (hδ : δ < 0) :
    Integrable (fun x ↦ if 0 ≤ x then rexp (δ * x) else 0) volume := by
  suffices Integrable (exponentialPDFReal (-δ)) volume by
    unfold exponentialPDFReal gammaPDFReal at this
    simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one] at this
    simp_rw [itemul] at this
    rw [integrable_const_mul_iff] at this
    · ring_nf at this ⊢
      exact this
    · refine isUnit_iff_exists_inv.mpr ?_
      use (-δ)⁻¹
      field_simp
      simp
      linarith
  refine exponentialPDFReal_integrable (show 0 < -δ by linarith)

lemma ruin_rewrite {α β c : ℝ} (hα : 0 < α) (hc : 0 < c)
  (hβ : β = 1) (what : β⁻¹ < α / c + β)
  (gen₂ : β * (α + c * β) - c ≠ 0) {u : ℝ} (hu : u ≥ 0) (t : ℝ) :
  (if 0 ≤ t then
      ∫ (x : ℝ) in Set.Iic (u + c * t),
        (1 - α * β / c * rexp ((α / c - β⁻¹) * (u + c * t - x))) * exponentialPDFReal β x
    else 0) =
    if 0 ≤ t then
      1 - rexp (-(β * (u + c * t))) -
        α * β ^ 2 / c * rexp ((α / c - β⁻¹) * (u + c * t)) *
          ((α / c + β - β⁻¹)⁻¹ * (1 - rexp (-((α / c + β - β⁻¹) * (u + c * t)))))
    else 0 := by

      split_ifs with g₀
      · unfold exponentialPDFReal gammaPDFReal
        simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one, mul_ite, mul_zero]
        simp_rw [sub_mul]
        simp only [one_mul, neg_sub]
        have (x z : ℝ) : α * β / c * z * (β * rexp (-(β * x)))
                       = α * β ^ 2 / c * z * (rexp (-(β * x))) := by ring_nf
        simp_rw [this]
        simp_rw [mul_assoc]
        simp_rw [← exp_add]
        have (x : ℝ) : α / c * (u + c * t - x) =
                      (α / c * (u + c * t)) - α / c * (x) := by nth_rw 1 [mul_sub]
        simp_rw [this]
        simp_rw [ite_sub']
        rw [integral_sub]
        · have : (∫ (a : ℝ) in Set.Iic (u + c * t),
            if 0 ≤ a then β * rexp (-(β * a)) else 0)
           = (∫ (a : ℝ) in Set.Iic (u + c * t), exponentialPDFReal β a) := by
            unfold exponentialPDFReal gammaPDFReal
            simp
          rw [this]
          rw [← ProbabilityTheory.cdf_expMeasure_eq_integral]
          · rw [cdf_expMeasure_eq]
            · have (a : ℝ) : (α / c * (u + c * t) - α / c * a - β⁻¹ * (u + c * t - a) + -(β * a)) =
                            ((α / c - β⁻¹) * (u + c * t) + (β⁻¹ - (α / c + β)) * a) := by
                    field_simp
                    ring_nf
              simp_rw [this, exp_add, itemul, ← mul_assoc]
              rw [integral_const_mul]
              have (a : ℝ) :
                (if 0 ≤ a then rexp ((β⁻¹ - (α / c + β)) * a) else 0)
                = (-(β⁻¹ - (α / c + β)))⁻¹ *
                exponentialPDFReal (-(β⁻¹ - (α / c + β))) a := by
                    unfold exponentialPDFReal gammaPDFReal
                    simp
                    field_simp
                    congr
                    field_simp
                    congr
                    ring_nf
              simp_rw [this]
              rw [integral_const_mul]
              rw [← ProbabilityTheory.cdf_expMeasure_eq_integral]
              · rw [cdf_expMeasure_eq]
                · have : 0 ≤ u + c * t := by
                    have : 0 ≤ c * t := by
                        apply mul_nonneg <;> linarith
                    calc 0 ≤ u := by tauto
                     _ ≤ u + (c * t) := by linarith
                  repeat rw [if_pos this]
                  ring_nf
                simp only [neg_sub, sub_pos]
                exact what
              · simp only [neg_sub, sub_pos]
                exact what
            · linarith
          · linarith
        · refine Integrable.restrict ?_
          suffices  Integrable (exponentialPDFReal β) volume by
            unfold exponentialPDFReal gammaPDFReal at this
            convert this
            simp
          refine exponentialPDFReal_integrable ?_
          rw [hβ]
          simp
        · refine Integrable.restrict ?_
          simp_rw [itemul]
          rw [integrable_const_mul_iff]
          · -- rewrite the exponent as usual
            rw [hβ]
            simp
            ring_nf
            field_simp
            have (x : ℝ) :
                ((α * (c * t + u - x) - c ^ 2 * t - c * u) / c)
                = (α / c - 1) * (c * t + u) + (-α / c) * (x) := by
                    field_simp;ring_nf
            simp_rw [this]
            simp_rw [exp_add]
            simp_rw [itemul]
            rw [integrable_const_mul_iff]
            · apply integrableExp
              suffices - (α / c) < 0 by rw [neg_div];exact this
              simp only [Left.neg_neg_iff]
              apply div_pos <;> linarith
            · refine isUnit_iff_exists_inv.mpr ?_
              use (rexp ((α / c - 1) * (c * t + u)))⁻¹
              field_simp
          rw [hβ]
          simp
          constructor <;> linarith
      · rfl

theorem ruin_integrable {α : ℝ} (hα : 0 < α) :
  Integrable (fun a ↦ if 0 ≤ a then if 0 ≤ a then rexp (-(α * a)) else 0 else 0) volume := by
    suffices Integrable (fun a ↦ if 0 ≤ a then rexp (-(α * a)) else 0) volume by
        convert this using 1
        ext a
        simp only [ite_eq_left_iff, not_le, right_eq_ite_iff]
        intro h₀ h₁
        linarith
    have (a : ℝ) : - (α * a) = -α * a := by ring_nf
    simp_rw [this]
    apply integrableExp
    simp
    linarith

theorem ruin_integrable' {α c : ℝ} (hc : 0 < c) (u : ℝ) :
  Integrable (fun a ↦ if 0 ≤ a then
    if 0 ≤ a then rexp ((c * (-u - c * a) + α * u) / c) else 0 else 0) volume := by
    suffices Integrable (fun a ↦ if 0 ≤ a then rexp ((c * (-u - c * a) + α * u) / c) else 0) volume
        by
        convert this using 1
        ext a
        split_ifs <;> field_simp
    have (a : ℝ) : (c * (-u - c * a) + α * u) / c =
                    -c * a + (α * u / c - u) := by
        ring_nf;field_simp;ring_nf
    simp_rw [this]
    simp_rw [exp_add]
    simp_rw [mul_comm]
    simp_rw [itemul]
    rw [integrable_const_mul_iff]
    · have (a : ℝ) : a * -c = -c * a := by rw [mul_comm]
      simp_rw [this]
      apply integrableExp
      linarith
    · refine isUnit_iff_exists_inv.mpr ?_
      use (rexp (α * u / c - u))⁻¹
      field_simp

lemma split_ite {α β c : ℝ} (u : ℝ) :
  ∫ (t : ℝ),
      exponentialPDFReal α t *
        ∫ (x : ℝ) in Set.Iic (u + c * t),
          (1 - α * β / c * rexp ((α / c - β⁻¹) * (u + c * t - x))) * exponentialPDFReal β x =
    ∫ (t : ℝ),
      (if 0 ≤ t then α ^ 1 / Gamma 1 * t ^ (1 - 1) * rexp (-(α * t)) else 0) *
        if 0 ≤ t then
          ∫ (x : ℝ) in Set.Iic (u + c * t),
            (1 - α * β / c * rexp ((α / c - β⁻¹) * (u + c * t - x))) * exponentialPDFReal β x
        else 0 := by
        unfold exponentialPDFReal gammaPDFReal
        congr
        ext t
        simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one, mul_ite, mul_zero,
        ite_mul, zero_mul, pow_one, tsub_self, pow_zero, left_eq_ite_iff, not_le, ite_eq_right_iff,
        mul_eq_zero, exp_ne_zero, or_false]
        intro h₀ h₁
        linarith

/-- This verifies a claim from Wikipedia at the end of
https://en.wikipedia.org/wiki/Ruin_theory#Classical_model
β = claim size limitation rate (1 / $); 1/β=E(claim size) = $ = μ
λ = α = claim arrival rate (1/time); 1/α=E(claim time)=time
u = initial capital
φ(u)=nonruin probability

Units checK;
λ = 1 / hour        = α
c = $ / hour
λ / c = 1 / $
μ = $               = 1 / β
λ μ / c = 1         = α / (β * c)
1/μ - λ/c = 1/$ - 1/$
The following lemma is correct but was written
with an incorrect generalization in mind so it looks complicated.
-/
lemma ruin_theory_classical_model_solution₁ {α c : ℝ} {φ : ℝ → ℝ}
    (hα : 0 < α) (hc : 0 < c)
    (h : φ = fun u => 1 - ((α * 1) / c) * Real.exp (-(1 / 1 - α / c) * u)) :
    integralEquation α 1 c φ := by
  unfold integralEquation
  have what : 1⁻¹ < α / c + 1 := by
    simp_all
  have gen₂ : (1 * (α + c * 1) - c) ≠ 0 := by
    have : 1 * 1⁻¹ < 1 * (α / c + 1) :=
        mul_lt_mul_of_nonneg_of_pos' (by simp) what (by simp) (by linarith)
    field_simp at this
    linarith
  intro u hu
  have g₀ (t : ℝ) : ((α - c) * (u + c * t) / c + -(α * (u + c * t) / c))
               = (-1) * (u + c * t):= by field_simp; ring_nf
  have g₁ (t : ℝ) : α * rexp (-(α * t)) * rexp (-(c * t) + -u)
               = α * rexp (-((α * t) + c * t + u)) := by
    rw [mul_assoc]
    congr
    rw [← exp_add]
    apply congrArg
    linarith
  have g₂ (t : ℝ) : α * rexp (-(α * t)) * (rexp (-(c * t)) * rexp (-u))
               = α * (rexp (-(α * t) + (-(c * t) + -u))) := by
    rw [exp_add, mul_assoc, exp_add]
  have g₃ (t : ℝ) : α * rexp (-(α * t)) * rexp ((α - c) * (u + c * t) / c)
               = α * rexp (-(α * t) + ((α - c) * (u + c * t) / c)) := by
    rw [exp_add, mul_assoc]
  rw [h]
  simp only [one_div, neg_sub]
  rw [split_ite]
  simp_rw [ruin_rewrite hα hc (by sorry) what gen₂ hu, mul_sub]
  simp only [pow_one, Gamma_one, div_one, tsub_self, pow_zero, mul_one, mul_ite, ite_mul, zero_mul,
    mul_zero]
  field_simp
  simp only [mul_one, one_mul, neg_add_rev, one_pow, add_sub_cancel_right]
  field_simp
  simp_rw [mul_sub, ← exp_add, g₀, exp_add, mul_one, neg_mul, one_mul, neg_add_rev, g₁, g₂, g₃]
  field_simp
  ring_nf
  field_simp
  simp_rw [itemul, ite_sub']
  rw [integral_const_mul, integral_sub]
  · repeat rw [ite_ite]
    have h₀ (a : ℝ) : (c * (-u - c * a) + α * u) / c
               = (- c * a) + (-u + α * u / c) := by field_simp;ring_nf
    have h₁ (a : ℝ) : rexp (-c * a) * (rexp (-u) * rexp (α * u / c))
     =  (rexp (-u) * rexp (α * u / c)) * rexp (-c * a) := by ring_nf
    have h₂ : (∫ (a : ℝ), if 0 ≤ a then rexp (-c * a) else 0) =
            ∫ (a : ℝ), (1/c) * exponentialPDFReal c a := by
        unfold exponentialPDFReal gammaPDFReal
        simp only [neg_mul, one_div, rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one,
          mul_ite, mul_zero]
        congr
        ext a
        congr
        field_simp
    have h₃ : (∫ (a : ℝ), if 0 ≤ a then rexp (-(α * a)) else 0) =
            ∫ (a : ℝ), (1 / α) * exponentialPDFReal α a := by
        unfold exponentialPDFReal gammaPDFReal
        simp only [one_div, rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one, mul_ite,
          mul_zero]
        congr
        ext a
        ring_nf
        field_simp
    simp_rw [h₃]
    rw [integral_const_mul, integral_exponentialPDFReal_eq_one α hα]
    ring_nf
    field_simp
    simp_rw [h₀, exp_add, h₁, itemul, integral_const_mul, h₂, integral_const_mul]
    field_simp
    rw [integral_exponentialPDFReal_eq_one c hc, mul_one, sub_right_inj, mul_assoc]
    congr
    rw [← exp_add]
    congr
    field_simp -- wow!
  · apply ruin_integrable hα
  · apply ruin_integrable' <| RCLike.ofReal_pos.mp hc


lemma ruin_theory_classical_model_solution {α β c : ℝ} {φ : ℝ → ℝ}
    (hα : 0 < α) (hc : 0 < c) (hβ : β = 1)
    (h : φ = fun u => 1 - (α / (β * c)) * Real.exp (-(β - α / c) * u)) :
    integralEquation α β c φ := by
  subst β
  apply ruin_theory_classical_model_solution₁
  tauto
  tauto
  rw [h]
  ext u
  ring_nf

lemma ruin_theory_classical_model_solution' {α β c : ℝ} {φ : ℝ → ℝ}
    (hα : 0 < α) (hc : 0 < c)
    (h : φ = fun u => 1 - (α / (β * c)) * Real.exp (-(β - α / c) * u)) :
    integralEquation α β c φ := by
  intro u hu
  rw [h]
  simp
  unfold exponentialPDFReal gammaPDFReal
  simp

  sorry
