constants α β γ : Type
constant f : α → β
constant g : β → γ
constant b : β

#check λ x : α, x        -- α → α
#check λ x : α, b        -- α → β
#check λ x : α, g (f x)  -- α → γ
#check λ x, g (f x)

#eval 12*12

def double : ℕ → ℕ := λ x, x + x
def square : ℕ → ℕ := λ x, x * x
def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)

def quadruple: ℕ → ℕ := λ x, do_twice double x
#reduce quadruple 9

def by_eight: ℕ → ℕ := λ x, double (quadruple x)
#reduce by_eight 7

/-
Define a function Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) which applies its argument twice, so that Do_Twice do_twice is a function that applies its input four times. Then evaluate Do_Twice do_twice double 2.
-/

def Do_twice: ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ)  := λ F f x, F (F f) x

#reduce Do_twice do_twice double 2

/-
Above, we discussed the process of “currying” a function, that is, taking a function f (a, b) that takes an ordered pair as an argument, and recasting it as a function f' a b that takes two arguments successively. As another exercise, we encourage you to complete the following definitions, which “curry” and “uncurry” a function.

try it!
-/

--Solutions
def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := λ a, (λ b, f(a,b))
def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ := λ p, f p.1 p.2

--To test, we create two functions
def add_projs: ℕ×ℕ→ℕ := λ p, p.1+p.2
#eval add_projs (3,22)  

def curried_add_projs: ℕ → ℕ → ℕ := λ x y, x+y
#eval curried_add_projs 3 22

--but for some reason they don't work
#reduce curry add_projs
#reduce uncurry curried_add_projs

--however if we change the types of the domain & range they work,
-- at least currying does. Didn't check uncurrying this way.
def curry_N (f : ℕ × ℕ → ℕ) : ℕ → ℕ → ℕ := λ a, (λ b, f(a,b))
#check curry_N
#reduce curry_N add_projs


#check list.nil
#check list.cons
#check list.append

/- Above, we used the example vec α n for vectors of elements of type α of length n. Declare a constant vec_add that could represent a function that adds two vectors of natural numbers of the same length, and a constant vec_reverse that can represent a function that 
reverses its argument. Use implicit arguments for parameters that can be inferred. Declare some variables and check some expressions involving the constants that you have declared. -/
-- namespace hidden
universe u
constant vec : Type u → ℕ → Type u
constant empt : Π α : Type u, vec α 0
constant cons :
  Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
constant vec_add : Π {α : Type u} {n : ℕ}, vec α n → vec α n → vec α n

constant vec_reverse : Π {α: Type u} {n: ℕ}, vec α n → vec α n

constant v : vec ℕ 2
#check @v
#check v
#check vec_add v v
#check vec_reverse v
#check vec_reverse (vec_add v v)
#check vec_add v (vec_reverse v)  
-- end hidden

-- universe u


/- 4. Similarly, declare a constant matrix so that matrix α m n could represent the type of m by n matrices. Declare some constants to represent functions on this type, such as matrix addition and multiplication, and (using vec) multiplication of a matrix by a vector. Once again, declare some variables and check some expressions involving the constants that you have declared. -/

constant matrix : Type u → ℕ → ℕ → Type u

constant mat_mul: Π {α : Type u} {m : ℕ} {n : ℕ} {k : ℕ}, matrix α m n → matrix α n k → matrix α m k
#check mat_mul

constant mat_vec_mul: Π {α : Type u} {m : ℕ} {n: ℕ} matrix α m n → vec α n → vec α m

