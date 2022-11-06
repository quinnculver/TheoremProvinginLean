
constants p q : Prop

theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
#print t1
#check t1
#reduce t1

theorem t2 : p → q → p :=
begin
  intros h g,
  show p, 
  from h,
  --apply h,
end


variables p q r : Prop
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
  (assume h : p ∧ (q ∨ r),
    have hp : p, from h.left,
    or.elim (h.right)
      (assume hq : q,
        show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨hp, hq⟩)
      (assume hr : r,
        show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨hp, hr⟩))
  (assume h : (p ∧ q) ∨ (p ∧ r),
    or.elim h
      (assume hpq : p ∧ q,
        have hp : p, from hpq.left,
        have hq : q, from hpq.right,
        show p ∧ (q ∨ r), from ⟨hp, or.inl hq⟩)
      (assume hpr : p ∧ r,
        have hp : p, from hpr.left,
        have hr : r, from hpr.right,
        show p ∧ (q ∨ r), from ⟨hp, or.inr hr⟩))

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
iff.intro
--we do each case slightly differently
  (assume h: p ∧ q,
    show (q ∧ p), from and.intro (and.right h) (and.left h)
  )
  (assume h: q ∧ p,
    have hq: q, from h.left,
    have hp: p, from h.right,
    show (p ∧ q), from and.intro hp hq
    --show (p ∧ q), from and.intro (and.right h) (and.left h)
  )
 
example : p ∨ q ↔ q ∨ p :=
iff.intro
--we do each case slightly differently
(assume h : p ∨ q,
  or.elim h
    (assume hp : p,
      show q ∨ p, from or.intro_right q hp
    )
    (assume hq : q,
      show q ∨ p, from or.intro_left p hq)
)
(assume h : q ∨ p,
  h.elim
    (assume hq : q, or.inr hq)
    (assume hp : p, or.inl hp)
)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
iff.intro
--first a hard-to-read way:
(assume h: (p ∧ q) ∧ r, 
    and.intro 
      (and.left (and.left h)) 
      (and.intro 
        (and.right (and.left h))
        (and.right h))
      
)
--second a more readable way:
(assume h: p ∧ (q ∧ r),
  have hp: p, from h.left,
  have hq: q, from (h.right).left,
  have hr: r, from (h.right).right,
  have hpq: p ∧ q, from and.intro hp hq,
  show (p ∧ q) ∧ r, from and.intro hpq hr
)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
(iff.intro
  (assume h : (p ∨ q) ∨ r,
  sorry
  )
  (sorry)
)


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
  (assume h : p ∧ (q ∨ r),
    have hp : p, from and.left h,
    have hqr : q ∨ r, from and.right h,
    or.elim hqr
    (assume hq: q,
      have hpq : p ∧ q, from ⟨hp, hq⟩,
      show (p ∧ q) ∨ (p ∧ r), from or.inl hpq
    )
    (assume hr: r,
      have hpr : p ∧ r, from ⟨hp, hr⟩,
      show (p ∧ q) ∨ (p ∧ r), from or.inr hpr
    )
  )
  (assume h : (p ∧ q) ∨ (p ∧ r),
    or.elim h 
    (assume hpq: p ∧ q,
      show p ∧ (q ∨ r), from 
        ⟨and.left hpq, or.inl (and.right hpq)⟩
    )
    (assume hpr: p ∧ r,
      show p ∧ (q ∨ r), from
        ⟨and.left hpr, or.inr (and.right hpr)⟩ 
    )  
  )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry

example : (¬p ∨ q) → (p → q) :=
begin
  intro h,
  cases h,
    exact (λ t:p, absurd t h),    
    exact (λ x, h),
end

example : p ∨ false ↔ p := 
begin
split,
  begin
    intro hpf,
    cases hpf,
        exact hpf,
      
        exfalso,
        exact hpf,
  end,
  begin
    intro hp,
    exact or.inl hp,
  end,
end



example : p ∧ false ↔ false := sorry
example : (p → q) → (¬q → ¬p) := sorry


/- Prove the following identities, replacing the “sorry” placeholders with actual proofs. These require classical reasoning.
 -/
open classical

variable s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
(assume h: (p → (r ∨ s)),
  by_cases
    (assume hp : p, 
      have hrs: r ∨ s, from h hp,
      or.elim hrs
      (assume hr: r,
        have hpr : p → r, from (λ hp : p, hr),
        or.inl hpr   
      )
      (assume hs: s,
        have hps : p → s, from (λ hp : p, hs),
        or.inr hps
      )
    )
    (assume hp : ¬p, 
      have hpr : p → r, from (λ x : p, (absurd x hp)),
      or.inl hpr  
    )
)

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction
end


example : ¬(p ∧ q) → ¬p ∨ ¬q := 
begin
  intro h,
  by_cases hp : p,
  begin
    by_cases hq :q,
    begin
      have hpq : p ∧ q, from and.intro hp hq,
      exact absurd hpq h,
    end,

    begin
      exact or.inr hq,
    end,
  end,

  begin
    exact or.inl hp,
  end,  
end

example : ¬(p → q) → p ∧ ¬q := 
begin
  intro h,
  by_cases hp : p,
  begin
    by_cases hq : q,
    begin
      have hpq : p → q, from (λ x,  hq),
      exfalso,--absurd h hpq,
      apply h hpq,
    end,

    begin
      split,
      { assumption },
      --exact hp, 
      { assumption },
      --exact hq,
    end,
  end,

  begin
    by_cases hq : q,
    begin
      exfalso,
      have hpq : p → q, from (λ x, hq),
      apply h hpq,
    end,
    
    begin
      split,
      begin
        exfalso,
        have hpq : p → q, from (λ t : p, absurd t hp),
        apply h hpq,
      end,

      begin
        {assumption},
      end,
    end,
  end,
end

example : (p → q) → (¬p ∨ q) := 
begin
  intro hpq,
  by_cases hp : p,
  begin
    have hq : q, from hpq hp,
    exact or.inr hq,
  end,

  begin
    exact or.inl hp,
  end,
end


example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
begin
  intro h,
  by_cases hp : p,
    begin
      exact hp,
    end,

    begin
      have hpq : p → q, from (λ x : p, absurd x hp),
      apply h hpq,
    end,  
end
