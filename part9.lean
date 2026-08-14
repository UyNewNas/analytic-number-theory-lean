
/-! ## 8. The per-q assembly analysis: regrouping by reduced fractions -/

/-- gcd multiplication: gcd(a*c, b*c) = c * gcd(a, b). -/
lemma gcd_mul_right' (a b c : ℕ) : (a * c).gcd (b * c) = c * (a.gcd b) := by
  exact Nat.gcd_mul_right a b c

/-- Dividing by the gcd gives a coprime pair. -/
lemma coprime_div_gcd {q r : ℕ} (hq : 0 < q) : (q / q.gcd r).Coprime (r / q.gcd r) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hdiv : q.gcd r ∣ q := Nat.gcd_dvd_left q r
  have hdiv2 : q.gcd r ∣ r := Nat.gcd_dvd_right q r
  -- gcd(q, r) = gcd((q/g)·g, (r/g)·g) = g·gcd(q/g, r/g)
  have hcalc : (q / q.gcd r * (q.gcd r)).gcd (r / q.gcd r * (q.gcd r)) = q.gcd r := by
    rw [gcd_mul_right']
    rw [Nat.div_mul_cancel hdiv, Nat.div_mul_cancel hdiv2]
  -- g·gcd(q/g, r/g) = g ⟹ gcd(q/g, r/g) = 1
  have hcalc' : (q / q.gcd r).gcd (r / q.gcd r) = 1 := by
    -- from hcalc: (q/g).gcd (r/g) * g = g — cancel g
    have hmain : ((q / q.gcd r).gcd (r / q.gcd r)) * (q.gcd r) = (q.gcd r) := by
      simpa [mul_comm] using hcalc
    exact (mul_right_cancel₀ (Nat.ne_of_gt hg) hmain)
  exact hcalc'

/-- **Per-modulus regrouping (逐 q 装配的精确内容)**: for weights w(q),
    sum_{q <= Q} w(q) * sum_{r < q} f(r/q) = sum_{q' <= Q} W(q') * sum_{red r'} f(r'/q')
  with W(q') = sum_{d <= Q/q'} w(q'*d); the reduced fractions r'/q' (coprime) carry
  the regrouped weight. For w(q) = mu^2 3^omega phi(q)/q, W(1) ~ (log Q)^3 is
  unbounded — the per-q stacking cannot produce the (m + Q^2) shape. -/
lemma perModulus_regroup {Q : ℕ} (w : ℕ → ℝ) (f : ℝ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, w q * ∑ r ∈ Finset.range q, f ((r : ℝ) / (q : ℝ))) =
      ∑ q' ∈ Finset.Icc 1 Q,
        (∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d)) *
        ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'), f ((r' : ℝ) / (q' : ℝ)) := by
  -- both sides are the triple sum over (q', r', d) of w(q'*d) * f(r'/q'), grouped differently
  have hLeft : (∑ q ∈ Finset.Icc 1 Q, w q * ∑ r ∈ Finset.range q, f ((r : ℝ) / (q : ℝ))) =
      ∑ q' ∈ Finset.Icc 1 Q, ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'),
        ∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d) * f ((r' : ℝ) / (q' : ℝ)) := by
    -- bijection between (q, r) and (q', r', d)
    let s : Finset (Σ q : ℕ, ℕ) := (Finset.Icc 1 Q).sigma (fun q => Finset.range q)
    let t : Finset (Σ q' : ℕ, ℕ × ℕ) := (Finset.Icc 1 Q).sigma (fun q' =>
      ((Finset.range q').filter (fun r' => r'.Coprime q')).product (Finset.Icc 1 (Q / q')))
    have hbij : (∑ p ∈ s, w p.1 * f ((p.2 : ℝ) / (p.1 : ℝ))) =
        (∑ p ∈ t, w (p.1 * p.2.2) * f ((p.2.1 : ℝ) / (p.1 : ℝ))) := by
      rw [Finset.sum_bij (s := s) (t := t)
        (f := fun p : Σ q : ℕ, ℕ => w p.1 * f ((p.2 : ℝ) / (p.1 : ℝ)))
        (g := fun p : Σ q' : ℕ, ℕ × ℕ => w (p.1 * p.2.2) * f ((p.2.1 : ℝ) / (p.1 : ℝ)))
        (i := fun p _ => (⟨p.1 / p.1.gcd p.2, (p.2 / p.1.gcd p.2, p.1.gcd p.2)⟩ : Σ q' : ℕ, ℕ × ℕ))]
      · -- i p ∈ t
        intro p hp
        rw [Finset.mem_sigma] at hp
        rcases hp with ⟨hq, hr⟩
        rw [Finset.mem_sigma]
        -- q' = p.1 / g >= 1, <= Q; r' = p.2 / g < q'; d = g in Icc 1 (Q / q'); coprime
        let g := p.1.gcd p.2
        have hgpos : 0 < g := Nat.gcd_pos_of_pos_left p.2 (Finset.mem_Icc.mp hq).1
        have hgdiv1 : g ∣ p.1 := Nat.gcd_dvd_left p.1 p.2
        have hgdiv2 : g ∣ p.2 := Nat.gcd_dvd_right p.1 p.2
        have hq' : p.1 / g ∈ Finset.Icc 1 Q := by
          rw [Finset.mem_Icc]
          constructor
          · exact Nat.succ_le_of_lt (Nat.div_pos hgpos (le_of_lt (Finset.mem_Icc.mp hq).1))  -- hmm
          · exact le_trans (Nat.div_le_self p.1 g) (Finset.mem_Icc.mp hq).2
        have hd : g ∈ Finset.Icc 1 (Q / (p.1 / g)) := by
          rw [Finset.mem_Icc]
          constructor
          · exact hgpos
          · -- g <= Q / (p.1/g) ⟺ g·(p.1/g) <= Q ⟺ p.1 <= Q ✓
            have hgm : g * (p.1 / g) = p.1 := (Nat.mul_div_cancel' hgdiv1).symm
            rw [Nat.le_div_iff_mul_le (Nat.div_pos hgpos (le_of_lt (Finset.mem_Icc.mp hq).1))]
            rw [← hgm]
            exact (Finset.mem_Icc.mp hq).2
        have hr' : p.2 / g ∈ (Finset.range (p.1 / g)).filter (fun r' => r'.Coprime (p.1 / g)) := by
          rw [Finset.mem_filter, Finset.mem_range]
          constructor
          · -- p.2 / g < p.1 / g ⟸ p.2 < p.1
            exact Nat.div_lt_div_of_lt_of_dvd hr hgdiv2 hgdiv1  -- hmm — check
          · exact coprime_div_gcd (Finset.mem_Icc.mp hq).1
        exact ⟨hq', Finset.mem_product.mpr ⟨hr', hd⟩⟩
      · -- i_inj: reduced fractions unique
        intro p₁ hp₁ p₂ hp₂ h
        rw [Finset.mem_sigma] at hp₁ hp₂
        -- h : (p₁.1 / g₁, (p₁.2 / g₁, g₁)) = (p₂.1 / g₂, (p₂.2 / g₂, g₂))
        -- i.e. p₁.1/g₁ = p₂.1/g₂, p₁.2/g₁ = p₂.2/g₂, g₁ = g₂ where g₁ = p₁.1.gcd p₁.2
        sorry
      · -- i_surj
        intro p hp
        rw [Finset.mem_sigma] at hp
        rcases hp with ⟨hq', hp2⟩
        rcases (Finset.mem_product.mp hp2) with ⟨hr', hd⟩
        rw [Finset.mem_filter] at hr'
        -- preimage: (p.1 * p.2.2, p.2.1 * p.2.2)
        refine ⟨⟨p.1 * p.2.2, p.2.1 * p.2.2⟩, ?_, ?_⟩
        · rw [Finset.mem_sigma]
          constructor
          · rw [Finset.mem_Icc]
            constructor
            · exact Nat.succ_le_of_lt (lt_of_lt_of_le (Finset.mem_Icc.mp hq').1 (Nat.le_mul_of_pos_right _ (Finset.mem_Icc.mp hd).1))
            · -- p.1·p.2.2 <= Q: from d <= Q / q'
              have hle := (Finset.mem_Icc.mp hd).2
              rw [Nat.le_div_iff_mul_le (Finset.mem_Icc.mp hq').1] at hle
              simpa [mul_comm, mul_left_comm, mul_assoc] using hle
          · rw [Finset.mem_range]
            -- p.2.1·p.2.2 < p.1·p.2.2 ⟸ p.2.1 < p.1
            exact Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hr'.1) (Finset.mem_Icc.mp hd).1
        · -- i (q'·d, r'·d) = ⟨q', (r', d)⟩ — since gcd(q'd, r'd) = d (coprime)
          sorry
      · -- h: f p = g (i p)
        intro p hp
        -- w p.1 * f (p.2/p.1) = w ((p.1/g)*g) * f ((p.2/g)/(p.1/g))
        have hg : p.1 = (p.1 / p.1.gcd p.2) * p.1.gcd p.2 := by
          exact (Nat.div_mul_cancel (Nat.gcd_dvd_left p.1 p.2)).symm
        have hg2 : p.2 = (p.2 / p.1.gcd p.2) * p.1.gcd p.2 := by
          exact (Nat.div_mul_cancel (Nat.gcd_dvd_right p.1 p.2)).symm
        congr 1
        -- f (p.2/p.1) = f (p.2/g / (p.1/g)) — equal since p.2/p.1 = (p.2/g)/(p.1/g)
        congr 1
        -- p.2/p.1 = (p.2/g)/(p.1/g) — cross-multiply: (p.2/g)·p.1 = p.2·(p.1/g)
        -- hmm — from p.2 = (p.2/g)·g and p.1 = (p.1/g)·g:
        sorry
    -- then rewrite the LHS sum as the sigma sum, use hbij, then factor back
    sorry
  -- RHS factorization
  have hRight : (∑ q' ∈ Finset.Icc 1 Q,
        (∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d)) *
        ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'), f ((r' : ℝ) / (q' : ℝ))) =
      ∑ q' ∈ Finset.Icc 1 Q, ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'),
        ∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d) * f ((r' : ℝ) / (q' : ℝ)) := by
    apply Finset.sum_congr rfl
    intro q' hq'
    -- (Σ_d w)·(Σ_r' f) = Σ_{r',d} w·f — expand
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r' hr'
    rw [Finset.mul_sum]
  calc
    (∑ q ∈ Finset.Icc 1 Q, w q * ∑ r ∈ Finset.range q, f ((r : ℝ) / (q : ℝ))) = ... := hLeft
    _ = ... := hRight.symm
