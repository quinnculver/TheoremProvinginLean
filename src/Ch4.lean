import data.int.basic
import data.real.basic
import data.nat.basic

/- Prove the theorem below, using only the ring properties of ℤ enumerated in Section 4.2 and the theorem sub_self.
 -/

#check sub_self


example (x : ℤ) : x * 0 = 0 :=
/- calc
    x*0 = x*(0-0)   : by rw int.sub_self 0  
    ... = x*0 - x*0 : by rw mul_sub
    ... = 0         : by rw sub_self
 -/
begin
  rw ← int.sub_self 0,
  rw mul_sub,
  repeat{rw int.sub_self},  
end
/- 1. Prove these equivalences:
 -/
variables (α : Type*) (p q : α → Prop)

example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x  :=
assume h : ∀ x : α, p x ∧ q x,
assume z : α,
show p z, from and.elim_left (h z)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
exists.elim h
  (assume w,
    assume hw : p w ∧ q w,
    show ∃ x, q x ∧ p x, from ⟨w, hw.right, hw.left⟩)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
iff.intro
  (assume h : ∀ x, p x ∧ q x,
    show (∀ x, p x) ∧ (∀ x, q x), from and.intro
    (
      assume y,
      show p y, from and.elim_left (h y)    
    )
    (
      assume y,
      show q y, from and.elim_right (h y)    
    )
    
  )
  (assume h: (∀ x, p x) ∧ (∀ x, q x),
    assume y,
    show p y ∧ q y, from and.intro
    ((and.elim_left h) y)
    ((and.elim_right h)y)
  )



example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
begin
  intros h g,
  assume y,
  have py: p y, from g y,
  have pqy: p y → q y, from h y,
  apply pqy py,
end

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
begin
  intro h,
  assume y,
  cases h,
  begin
      have hp : p y, from h y,
      apply or.inl hp,
  end,

  begin
    have hq : q y, from h y,
    apply or.inr hq,
  end,
end

/-2. It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic):
 -/
variable r : Prop


example : α → ((∀ x : α, r) ↔ r) :=
begin
  assume y,
  split,
  begin
    intro h,
    apply (h y),
  end,

  begin
    intro h,
    exact (λ x, h),
  end,
  
end
 
open classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
begin
  split,
  begin
    intro h,
    by_cases hr : r,
    begin
      right,
      exact hr,
    end,
    begin
      left,
      assume y,
      have hpr : (p y ∨ r), from h y,
      show p y, from or.elim hpr 
                      (λ hpy, hpy)
                      (λ hr2, absurd hr2 hr)
    end,
  end,

  begin
    intro h,
    assume y,
    cases h,
    begin
      left,
      apply h y,
    end,

    begin
      right,
      exact h,
    end,
  end,
end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
begin
  split,
  begin
    intros h g,
    assume y,
    have hrp: (r → (p y)) , from  (h y),
    apply hrp g,
  end,

  begin
    intro h,
    assume y,
    intro g,
    have hp : (∀ (x : α), p x), from (h g),
    apply (hp y),
  end,
end


/- 3. Consider the “barber paradox,” that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction:
 -/

variables (men : Type*) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false := 
  begin
    have g: (shaves barber barber ↔ ¬ shaves barber barber), from (h barber),
    cases g,
    by_cases hs: (shaves barber barber),
    begin
      have hb: ¬shaves barber barber, from g_mp hs,
      apply hb hs,
    end,

    begin
      have hb: shaves barber barber, from g_mpr hs,
      apply hs hb,
    end,
  end

/-   5. Remember that, without any parameters, an expression of type Prop is just an assertion. Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions. For example, you can say that there are infinitely many primes by asserting that for every natural number n, there is a prime number greater than n. Goldbach’s weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary.
 -/


#check even

def prime (n : ℕ) : Prop := ∀ m : ℕ, m ∣ n → (m=1 ∨ m=n)

def infinitely_many_primes : Prop := ∀ n, ∃ m, (m > n) ∧ (prime n)

def Fermat_prime (n : ℕ) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry

--5. Prove as many of these as you can:
/- 
variables (α : Type*) (p q : α → Prop)
variable r : Prop -/

example : (∃ x : α, r) → r := 
begin

  intro h,
  cases h,
  exact h_h,
end

example (a : α) : r → (∃ x : α, r) :=
begin
  intro h,
  exact Exists.intro a h,
end

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro
(
  assume h : ∃ x, p x ∧ r,
  exists.elim h,
  assume w,
  have hpw :  p w from 
    have hp : ∃ x, p x from w
)
(
  sorry
)
/- begin
  split,
  begin
    intro h,
    cases e : h,
    cases h_h,
    exact ⟨Exists.intro _ h_h_left, h_h_right⟩,
    --have hp : ∃ (x:α), p x, from  Exists.intro _ h_h_left,
    --exact ⟨hp, h_h_right⟩
  end,
  begin
    intro h,
    cases h,
    cases h_left,
    have hpr: p_h_left_w ∧ r from and.intro (h_left_h h_right),
    -- ⟨h_left_h, h_right⟩,
  end,
end
 -/
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry


/- 6. Give a calculational proof of the theorem log_mul below. -/

variables log exp     : real → real
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc
  log (x * y) = log (exp( log x) * y) : (exp_log_eq hx)
          ... = log (exp( log x) * exp ( log y)) : (exp_log_eq hy)  
/-  ... = 
                 log (exp (log( x )) * exp (log( x ))) : 
                  by rw ← [exp_log_eq hx, exp_log_eq hy]
 -/
          ... = log(exp (log (x)+ log (y))) : 
                  by rw ← [exp_add, exp_add]
          
          ... = log(x) + log(y) : by  [exp_log_eq, exp_log_eq]


namespace hidden
variables (α : Type*) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨(w : α), (hw : p w ∧ q w)⟩ :=
  ⟨w, hw.right, hw.left⟩
end
end hidden