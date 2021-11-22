/-
Monday 11/15 Notes

*see lecture 27b*

single-value relation:
    - when an alpha maps to one beta, or multiple betas that equal eachother
    - ∀ (a : α), ∀ (b1, b2 : β), r a b1 → r a b2 → b1 = b2 

r is "defined at"...
    - all alphas that map to a beta
    - (a : α), ∃ b, r a b 

a relation is a function if...
    - r is single valued
    - i.e., it cannot be one-to-many

injective function:
    - cannot be many-to-one
        - example: sin(x) is not injective
            - passes vertical line test
            - fails horizontal line test

        - example: cubic function is injective
            - passes vertical line test
            - passes horizontal line test
    - ∀ (a1, a2 : α), ∀ (b : β), r a1 b → r a2 b → a1 = a2
    - invertible
            - the inverse of an injective function is always a valid single-value function

surjective function:
    - the image of its domain of definition is the entire codomain
    - ∀ (b : β), ∃ a, r a b
    - examples:
        - y = log x, viewed as a function from ℝ⁺ → ℝ⁺      yes
                - note: the definition of surjective
                includes totality, so it would not be
                true if we do not restrict the domain to
                the domain of definition
        - y = x^2, viewed as a function from ℝ → ℝ          no
        - y = x, viewed as a function from ℝ → ℝ            yes
        - y = sin x, viewed as a function from ℝ → ℝ        no
        - y = sin x, as a function from ℝ to [-1,1] ∈ ℝ     yes

bijective:
    - a function that is surjective and injective
    - the inverse is also a bijective function
    

    

-/
variables {α β γ : Type} (r : α → β → Prop)
local infix `≺`:50 := r


def single_valued := 
  ∀ {x : α} {y z : β}, r x y → r x z → y = z 


def function := single_valued r


def defined (a : α) := ∃ (b : β), r a b


def total_function := function r ∧ ∀ (a : α), defined r a
def strictly_partial_fun := function r ∧ ¬total_function r
def partial_function := function r -- includes total funs


def surjective := 
  total_function r ∧  
  ∀ (b : β), ∃ a : α, r a b


def injective := 
  total_function r ∧ 
  ∀ {x y : α} {z : β}, r x z → r y z → x = y


def bijective := surjective r ∧ injective r




/-
Wednesday 11/17 Notes


-/