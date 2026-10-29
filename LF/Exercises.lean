--  # Discussion Section 8: Programming and Theorem Proving in Lean
--
--  The following exercises are self-contained: this file imports nothing,
--  so you can open it directly in VS Code and work through it top to bottom.
--  Everything you need is defined right here — you will *not* need any lemmas
--  from Lean's standard library.
--
--  The only tactics you need are the ones from lecture:
--    - `rfl`        close a goal `a = a` (after evaluating both sides)
--    - `cases`      split a proof into one subgoal per constructor
--    - `rewrite`    rewrite the goal (or a hypothesis, with `... at h`)
--                   using an equation or a previously proved rule
--    - `intro`      name a `∀`-quantified variable or a hypothesis
--    - `exact`      close a goal with a matching hypothesis
--
--  Replace every `sorry` with a definition or proof. When you are
--  done, the file should contain no `sorry` and report no errors.


--  ===========================================================================
--  ## §1 — Traffic Lights
--  ===========================================================================

namespace TrafficLight

--  Just like `Day` and `RGB` in `Basics.lean`, a traffic light is an
--  enumerated type with finitely many values.

inductive Light : Type where
  | red
  | yellow
  | green

--  A real light cycles green → yellow → red → green → ...  The `next`
--  function sends each color to the one that comes after it.

def next (l : Light) : Light :=
  match l with
  | .green  => .yellow
  | .yellow => .red
  | .red    => .green

#eval next .green   -- expect: Light.yellow
#eval next .red     -- expect: Light.green

--  ### Exercise: isStop
--
--  Define `isStop`, which returns `true` exactly when the light is red
--  (i.e. when you must stop) and `false` otherwise. After you fill in the
--  definition, the two `theorem`s below should be accepted with no changes.

def isStop (l : Light) : Bool :=
  match l with
  | .red => true
  | .yellow => false
  | .green => false

theorem isStop_red   : isStop .red   = true  := by rfl
theorem isStop_green : isStop .green = false := by rfl

--  ### Exercise: next_three
--
--  After three steps, a light returns to where it started. State it as a
--  property of *every* light `l` and prove it.

theorem next_three : ∀ l, next (next (next l)) = l := by
  intro l
  cases l with
  | red => rfl
  | green => rfl
  | yellow => rfl

end TrafficLight


--  ===========================================================================
--  ## §2 — Booleans
--  ===========================================================================
--
--  Here we use Lean's built-in `Bool` (with values `true` and `false`),
--  just as `Basics.lean` does after introducing `MyBool`.

namespace Booleans

--  ### Exercise: myXor
--
--  Define *exclusive or* ("xor"): it returns `true` when exactly one of its
--  two arguments is `true`, and `false` otherwise.
--
--  Once your definition is correct, the four tests below should pass
--  unchanged.

def myXor (b1 b2 : Bool) : Bool :=
  match (b1, b2) with
  | (true, true) => false
  | (true, false) => true
  | (false, true) => true
  | (false, false) => false

theorem myXor_test1 : myXor true  true  = false := by rfl
theorem myXor_test2 : myXor true  false = true  := by rfl
theorem myXor_test3 : myXor false true  = true  := by rfl
theorem myXor_test4 : myXor false false = false := by rfl


--  ### Exercise: myXor_self
--
--  Anything xor'd with itself is `false`. Prove it for every `b`.

theorem myXor_self (b : Bool) : myXor b b = false := by
  cases b with
  | true => rfl
  | false => rfl


--  ### Exercise: myXor_false
--
--  `false` is a unit for xor: `myXor b false = b` for every `b`.

theorem myXor_false (b : Bool) : myXor b false = b := by
  cases b with
  | true => rfl
  | false => rfl


--  ### Exercise: myXor_comm
--
--  Xor is commutative. Prove it for all `b` and `c`.

theorem myXor_comm (b c : Bool) : myXor b c = myXor c b := by
  cases b with
  | true =>
    cases c with
    | true => rfl
    | false => rfl
  | false =>
    cases c with
    | true => rfl
    | false => rfl


--  ### Exercise: myXor_cancel (optional)
--
--  Xor is its own inverse: xor-ing by `b` twice cancels out.

theorem myXor_cancel (b c : Bool) : myXor b (myXor b c) = c := by
  sorry


--  ### Exercise: identity_fn_applied_twice (optional)
--
--  This one is about an *unknown* boolean function `f`. If `f` is the
--  identity on every input, then applying it twice is also the identity.

theorem identity_fn_applied_twice
    (f : Bool → Bool) (h : ∀ x : Bool, f x = x) (b : Bool) :
    f (f b) = b := by
  sorry

end Booleans

--  ---------------------------------------------------------------------------
--  ### §3 — Natural numbers
--  ---------------------------------------------------------------------------
--
--  Finally, a few exercises on our own natural numbers. We wrap everything
--  in a namespace so our names don't clash with Lean's built-in `Nat`.

namespace Numbers

inductive MyNat : Type where
  | zero
  | succ (n : MyNat)

--  `double n` adds `n` to itself by turning each `succ` into two `succ`s.

def double (n : MyNat) : MyNat :=
  match n with
  | .zero    => .zero
  | .succ n' => .succ (.succ (double n'))


--  ### Exercise: double's simplification rules
--
--  `double` matches on two cases, so it has two simplification rules.

theorem double_zero : double .zero = .zero := by sorry

theorem double_succ (n : MyNat) :
    double (.succ n) = .succ (.succ (double n)) := by sorry


--  `add` is defined by recursion on its second argument.

def add (n m : MyNat) : MyNat :=
  match m with
  | .zero    => n
  | .succ m' => .succ (add n m')


--  ### Exercise: add's simplification rules

theorem add_zero (n : MyNat) : add n .zero = n := by sorry
theorem add_succ (n m : MyNat) :
    add n (.succ m) = .succ (add n m) := by sorry


--  Now we seal both functions: later proofs must use the rules above.

attribute [irreducible] double add

--  `isZero` is a small helper that only inspects the *top* constructor.

def isZero (n : MyNat) : Bool :=
  match n with
  | .zero   => true
  | .succ _ => false


--  ### Exercise: isZero_double
--
--  Prove that doubling a number does not change whether it is zero.

theorem isZero_double (n : MyNat) : isZero (double n) = isZero n := by
  sorry


--  ### Exercise: add_cong
--
--  Prove that if `n = m` and `m = o`, then `add n m` and `add m o` are equal.

theorem add_cong (n m o : MyNat) (h1 : n = m) (h2 : m = o) :
    add n m = add m o := by
  sorry


--  ### Exercise: add_one_one (optional)
--
--  A concrete calculation, in the style of `one_plus_one_eq_two`. Because
--  `add` is now `irreducible`, you cannot use `rfl` directly.

def one : MyNat := .succ .zero
theorem one_eq : one = .succ .zero := by rfl

theorem add_one_one : add one one = .succ (.succ .zero) := by
  sorry

end Numbers
