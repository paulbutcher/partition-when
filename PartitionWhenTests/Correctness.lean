import PartitionWhen.Basic

namespace List

/-! ### Correctness of `partitionWhen`

Four properties that together pin down what "partition, starting a new
sublist whenever `p` fires" means, independent of any one implementation:

1. `partitionWhen_flatten` — no element is lost, duplicated, or reordered.
2. `partitionWhen_ne_nil_of_mem` — no group is spuriously empty.
3. `partitionWhen_tail_false` — groups are maximal: nothing inside a group
   (past its own head) should have split off.
4. `partitionWhen_head_true` — groups are complete: every group after the
   first genuinely starts at a trigger.

Together with two "cheap extra" corollaries (`partitionWhen_nil`,
`partitionWhen_length_flatten`). -/

@[simp] theorem partitionWhen_nil {α : Type _} (p : α → Bool) :
    partitionWhen p ([] : List α) = [] := rfl

/-- The overall result is nonempty for nonempty input. A prerequisite for the
four theorems below: it rules out the impossible `| [] => [[x]]` branch of
`partitionWhen` at every step of their inductive proofs. -/
theorem partitionWhen_ne_nil {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), xs ≠ [] → partitionWhen p xs ≠ [] := by
  intro xs
  induction xs using partitionWhen.induct (p := p) with
  | case1 => simp
  | case2 x => simp [partitionWhen]
  | case3 x y rest g gs heq hpy ih => simp [partitionWhen, heq, hpy]
  | case4 x y rest g gs heq hpy ih => simp [partitionWhen, heq, hpy]
  | case5 x y rest heq ih =>
    exact absurd heq (ih (by simp))

/-- Restates the `x :: y :: rest`, `p y = true` equation of `partitionWhen`
without the `match`, for use as a rewrite in the theorems below. -/
theorem partitionWhen_eq_case3 {α : Type _} (p : α → Bool) (x y : α) (rest g : List α)
    (gs : List (List α)) (heq : partitionWhen p (y :: rest) = g :: gs) (hpy : p y = true) :
    partitionWhen p (x :: y :: rest) = [x] :: g :: gs := by
  simp only [partitionWhen]; rw [heq]; simp [hpy]

/-- As `partitionWhen_eq_case3`, for the `p y = false` equation. -/
theorem partitionWhen_eq_case4 {α : Type _} (p : α → Bool) (x y : α) (rest g : List α)
    (gs : List (List α)) (heq : partitionWhen p (y :: rest) = g :: gs) (hpy : ¬ p y = true) :
    partitionWhen p (x :: y :: rest) = (x :: g) :: gs := by
  simp only [partitionWhen]; rw [heq]; simp [hpy]

/-- The first group of a partition always starts with the input's own first
element — needed for `partitionWhen_tail_false`'s `x :: y :: rest`,
`p y = false` case, where merging `x` onto the front of `g` requires knowing
`g`'s own head (not just its tail, which `partitionWhen_tail_false`'s
induction hypothesis covers) also fails `p`. -/
theorem partitionWhen_head?_head? {α : Type _} (p : α → Bool) :
    ∀ (x : α) (xs : List α), ((partitionWhen p (x :: xs)).head?.bind List.head?) = some x := by
  intro x xs
  cases xs with
  | nil => simp [partitionWhen]
  | cons y rest =>
    cases h : partitionWhen p (y :: rest) with
    | nil => exact absurd h (partitionWhen_ne_nil p (y :: rest) (by simp))
    | cons g gs => simp only [partitionWhen, h]; split <;> simp

theorem partitionWhen_flatten {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), (partitionWhen p xs).flatten = xs := by
  intro xs
  induction xs using partitionWhen.induct (p := p) with
  | case1 => simp [partitionWhen]
  | case2 x => simp [partitionWhen]
  | case3 x y rest g gs heq hpy ih =>
    rw [partitionWhen_eq_case3 p x y rest g gs heq hpy, flatten_cons, ← heq, ih]
    simp
  | case4 x y rest g gs heq hpy ih =>
    rw [partitionWhen_eq_case4 p x y rest g gs heq hpy, flatten_cons, cons_append, ← flatten_cons,
      ← heq, ih]
  | case5 x y rest heq ih =>
    exact absurd heq (partitionWhen_ne_nil p (y :: rest) (by simp))

theorem partitionWhen_length_flatten {α : Type _} (p : α → Bool) (xs : List α) :
    (partitionWhen p xs).flatten.length = xs.length := by
  rw [partitionWhen_flatten]

theorem partitionWhen_ne_nil_of_mem {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), ∀ g ∈ partitionWhen p xs, g ≠ [] := by
  intro xs
  induction xs using partitionWhen.induct (p := p) with
  | case1 => simp [partitionWhen]
  | case2 x => simp [partitionWhen]
  | case3 x y rest g gs heq hpy ih =>
    rw [partitionWhen_eq_case3 p x y rest g gs heq hpy]
    intro h hmem
    rcases mem_cons.mp hmem with rfl | hmem
    · simp
    · exact ih h (heq ▸ hmem)
  | case4 x y rest g gs heq hpy ih =>
    rw [partitionWhen_eq_case4 p x y rest g gs heq hpy]
    intro h hmem
    rcases mem_cons.mp hmem with rfl | hmem
    · simp
    · exact ih h (heq ▸ mem_cons_of_mem g hmem)
  | case5 x y rest heq ih =>
    exact absurd heq (partitionWhen_ne_nil p (y :: rest) (by simp))

theorem partitionWhen_tail_false {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), ∀ g ∈ partitionWhen p xs, ∀ z ∈ g.tail, p z = false := by
  intro xs
  induction xs using partitionWhen.induct (p := p) with
  | case1 => simp [partitionWhen]
  | case2 x => simp [partitionWhen]
  | case3 x y rest g gs heq hpy ih =>
    rw [partitionWhen_eq_case3 p x y rest g gs heq hpy]
    intro h hmem
    rcases mem_cons.mp hmem with rfl | hmem
    · simp
    · exact ih h (heq ▸ hmem)
  | case4 x y rest g gs heq hpy ih =>
    rw [partitionWhen_eq_case4 p x y rest g gs heq hpy]
    intro h hmem
    rcases mem_cons.mp hmem with rfl | hmem
    · have g_head : g.head? = some y := by
        have h2 := partitionWhen_head?_head? p y rest
        rwa [heq] at h2
      obtain ⟨ys, hg⟩ := List.head?_eq_some_iff.mp g_head
      subst hg
      have hprest := ih (y :: ys) (heq ▸ mem_cons_self ..)
      simp only [tail_cons] at hprest ⊢
      intro z hz
      rcases mem_cons.mp hz with rfl | hz
      · simpa using hpy
      · exact hprest z hz
    · exact ih h (heq ▸ mem_cons_of_mem g hmem)
  | case5 x y rest heq ih =>
    exact absurd heq (partitionWhen_ne_nil p (y :: rest) (by simp))

theorem partitionWhen_head_true {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), ∀ g ∈ (partitionWhen p xs).tail, ∀ z, g.head? = some z → p z = true := by
  intro xs
  induction xs using partitionWhen.induct (p := p) with
  | case1 => simp [partitionWhen]
  | case2 x => simp [partitionWhen]
  | case3 x y rest g gs heq hpy ih =>
    rw [partitionWhen_eq_case3 p x y rest g gs heq hpy]
    simp only [tail_cons]
    intro h hmem z hz
    rcases mem_cons.mp hmem with rfl | hmem
    · have h2 := partitionWhen_head?_head? p y rest
      rw [heq] at h2
      simp only [head?_cons, Option.bind_some] at h2
      rw [hz] at h2
      cases h2
      exact hpy
    · exact ih h (by rw [heq]; simpa using hmem) z hz
  | case4 x y rest g gs heq hpy ih =>
    rw [partitionWhen_eq_case4 p x y rest g gs heq hpy]
    simp only [tail_cons]
    intro h hmem z hz
    exact ih h (by rw [heq]; simpa using hmem) z hz
  | case5 x y rest heq ih =>
    exact absurd heq (partitionWhen_ne_nil p (y :: rest) (by simp))

/-! ### Equivalence of the other implementations to `partitionWhen`

Rather than proving each implementation equal to `partitionWhen` by a
direct induction (which would have to simulate two differently-shaped
recursions step by step), we go through the spec: `partitionWhen_unique`
says any `groups` satisfying the four properties above equals
`partitionWhen p xs`. So proving an implementation equal to
`partitionWhen` reduces to proving it satisfies those same four
properties — which is exactly the kind of proof already done above, just
adapted to a different recursion. -/

/-- The head of the first group of any spec-satisfying grouping of a
nonempty list is the list's own head — used to pin down where `groups` must
split in `partitionWhen_unique`'s `x :: y :: rest` cases. -/
theorem groups_head_eq_of_flatten {α : Type _} (groups : List (List α))
    (hne : ∀ g ∈ groups, g ≠ []) (a : α) (rest : List α) (hflat : groups.flatten = a :: rest) :
    ∃ g gs, groups = g :: gs ∧ g.head? = some a := by
  cases groups with
  | nil => simp at hflat
  | cons g gs =>
    refine ⟨g, gs, rfl, ?_⟩
    have hgne : g ≠ [] := hne g (mem_cons_self ..)
    obtain ⟨b, g', hg⟩ := exists_cons_of_ne_nil hgne
    subst hg
    simp only [flatten_cons, cons_append] at hflat
    obtain ⟨hab, -⟩ := List.cons.injEq .. |>.mp hflat
    simp [hab]

/-- Any `groups` satisfying the four spec properties (flatten, nonempty
members, tail elements fail `p`, later heads pass `p`) equals
`partitionWhen p xs`. Proved by the same case analysis as
`partitionWhen`'s own defining equations: `[]`, `[x]`, and
`x :: y :: rest` split by whether `p y` holds — except here the shape of
`groups` itself has to be *derived* from the spec at each step, rather than
read off a `match`. -/
theorem partitionWhen_unique {α : Type _} (p : α → Bool) :
    ∀ (xs : List α) (groups : List (List α)),
      groups.flatten = xs →
      (∀ g ∈ groups, g ≠ []) →
      (∀ g ∈ groups, ∀ y ∈ g.tail, p y = false) →
      (∀ g ∈ groups.tail, ∀ z, g.head? = some z → p z = true) →
      groups = partitionWhen p xs := by
  intro xs
  induction xs using partitionWhen.induct (p := p) with
  | case1 =>
    intro groups hflat hne _ _
    cases groups with
    | nil => rfl
    | cons g gs =>
      exfalso
      have hgne : g ≠ [] := hne g (mem_cons_self ..)
      simp only [flatten_cons] at hflat
      exact hgne (append_eq_nil_iff.mp hflat).1
  | case2 x =>
    intro groups hflat hne htail hhead
    obtain ⟨G, Gs, hG, hGhead⟩ := groups_head_eq_of_flatten groups hne x [] hflat
    subst hG
    obtain ⟨y', G', hG'⟩ := exists_cons_of_ne_nil (hne G (mem_cons_self ..))
    subst hG'
    simp only [head?_cons, Option.some.injEq] at hGhead
    subst hGhead
    simp only [flatten_cons, cons_append, cons.injEq] at hflat
    obtain ⟨-, hrest⟩ := hflat
    obtain ⟨hG'nil, hGsflat⟩ := append_eq_nil_iff.mp hrest
    subst hG'nil
    cases Gs with
    | nil => simp [partitionWhen]
    | cons g2 gs2 =>
      exfalso
      have hg2ne : g2 ≠ [] := hne g2 (mem_cons_of_mem _ (mem_cons_self ..))
      simp only [flatten_cons] at hGsflat
      exact hg2ne (append_eq_nil_iff.mp hGsflat).1
  | case3 x y rest g gs heq hpy ih =>
    intro groups hflat hne htail hhead
    obtain ⟨G, Gs, hG, hGhead⟩ := groups_head_eq_of_flatten groups hne x (y :: rest) hflat
    subst hG
    obtain ⟨x', G', hG'⟩ := exists_cons_of_ne_nil (hne G (mem_cons_self ..))
    subst hG'
    simp only [head?_cons, Option.some.injEq] at hGhead
    subst hGhead
    simp only [flatten_cons, cons_append, cons.injEq] at hflat
    obtain ⟨-, hrest⟩ := hflat
    have hG'nil : G' = [] := by
      cases G' with
      | nil => rfl
      | cons y' G'' =>
        exfalso
        simp only [cons_append, cons.injEq] at hrest
        have hy'y : y' = y := hrest.1
        have hpy' : p y' = false := htail (x' :: y' :: G'') (mem_cons_self ..) y' (by simp)
        rw [hy'y] at hpy'
        rw [hpy'] at hpy
        simp at hpy
    subst hG'nil
    simp only [nil_append] at hrest
    have hGseq := ih Gs hrest
      (fun h hm => hne h (mem_cons_of_mem _ hm))
      (fun h hm => htail h (mem_cons_of_mem _ hm))
      (fun h hm z hz => hhead h (mem_of_mem_tail hm) z hz)
    rw [hGseq, heq, partitionWhen_eq_case3 p x' y rest g gs heq hpy]
  | case4 x y rest g gs heq hpy ih =>
    intro groups hflat hne htail hhead
    obtain ⟨G, Gs, hG, hGhead⟩ := groups_head_eq_of_flatten groups hne x (y :: rest) hflat
    subst hG
    obtain ⟨x', G', hG'⟩ := exists_cons_of_ne_nil (hne G (mem_cons_self ..))
    subst hG'
    simp only [head?_cons, Option.some.injEq] at hGhead
    subst hGhead
    simp only [flatten_cons, cons_append, cons.injEq] at hflat
    obtain ⟨-, hrest⟩ := hflat
    have hG'ne : G' ≠ [] := by
      cases hG'nil : G' with
      | cons _ _ => simp
      | nil =>
        exfalso
        rw [hG'nil, nil_append] at hrest
        obtain ⟨g2, gs2, hGs, hg2head⟩ := groups_head_eq_of_flatten Gs
          (fun h hm => hne h (mem_cons_of_mem _ hm)) y rest hrest
        have hpy' := hhead g2 (by rw [hGs]; exact mem_cons_self ..) y hg2head
        exact hpy hpy'
    obtain ⟨y', G'', hG''⟩ := exists_cons_of_ne_nil hG'ne
    subst hG''
    simp only [cons_append, cons.injEq] at hrest
    obtain ⟨hy'y, hrest2⟩ := hrest
    subst hy'y
    have hGseq := ih ((y' :: G'') :: Gs)
      (by simp [flatten_cons, hrest2])
      (by
        intro h hm
        rcases mem_cons.mp hm with rfl | hm
        · simp
        · exact hne h (mem_cons_of_mem _ hm))
      (by
        intro h hm z hz
        rcases mem_cons.mp hm with rfl | hm
        · exact htail (x' :: y' :: G'') (mem_cons_self ..) z (mem_cons_of_mem _ hz)
        · exact htail h (mem_cons_of_mem _ hm) z hz)
      hhead
    rw [heq] at hGseq
    obtain ⟨hgeq, hgseq⟩ := List.cons.injEq .. |>.mp hGseq
    rw [partitionWhen_eq_case4 p x' y' rest g gs heq hpy, ← hgeq, ← hgseq]
  | case5 x y rest heq ih =>
    intro groups _ _ _ _
    exact absurd heq (partitionWhen_ne_nil p (y :: rest) (by simp))

/-! ### Equivalence of `partitionWhenTR` to `partitionWhen`

`partitionWhenTR` doesn't share a recursion shape with anything proved so
far — it processes one element at a time (like `partitionWhen`) but
via an accumulator instead of lookahead (unlike it), so neither the
"same-shape direct comparison" trick used for `partitionWhenSpan` nor a
straightforward induction applies. The spec properties have to be proved
about `go xs cur acc` for *arbitrary* `cur`/`acc`, not just the initial
`[] []`, which means each property needs an extra hypothesis describing what
`cur`/`acc` must already look like for the property to keep holding one step
further into the recursion — a loop invariant. -/

theorem go_flatten {α : Type _} (p : α → Bool) :
    ∀ (xs cur : List α) (acc : List (List α)),
      (partitionWhenTR.go p xs cur acc).flatten = acc.reverse.flatten ++ cur.reverse ++ xs := by
  intro xs
  induction xs with
  | nil =>
    intro cur acc
    unfold partitionWhenTR.go
    split
    · rename_i hcur
      have : cur = [] := isEmpty_iff.mp hcur
      simp [this]
    · simp [flatten_cons]
  | cons x xs ih =>
    intro cur acc
    unfold partitionWhenTR.go
    split
    · rw [ih]; simp [flatten_cons]
    · rw [ih]; simp

theorem go_ne_nil_of_mem {α : Type _} (p : α → Bool) :
    ∀ (xs cur : List α) (acc : List (List α)), (∀ g ∈ acc, g ≠ []) →
      ∀ g ∈ partitionWhenTR.go p xs cur acc, g ≠ [] := by
  intro xs
  induction xs with
  | nil =>
    intro cur acc hacc
    unfold partitionWhenTR.go
    split
    · rename_i hcur
      intro g hg
      exact hacc g (mem_reverse.mp hg)
    · rename_i hcur
      have hcurne : cur ≠ [] := by simpa using hcur
      intro g hg
      rw [mem_reverse, mem_cons] at hg
      rcases hg with rfl | hg
      · simpa using hcurne
      · exact hacc g hg
  | cons x xs ih =>
    intro cur acc hacc
    unfold partitionWhenTR.go
    split
    · rename_i h
      have hcurne : cur ≠ [] := by
        have := (Bool.and_eq_true .. |>.mp h).2
        simpa using this
      apply ih
      intro g hg
      rcases mem_cons.mp hg with rfl | hg
      · simpa using hcurne
      · exact hacc g hg
    · exact ih (x :: cur) acc hacc

/-- Companion to `partitionWhenTake_tail_false`'s "does the merged group's
own head, not just its tail, fail `p`?" concern — for `partitionWhenTR`, the
answer comes not from a lookup lemma but from the loop invariant `cur`
carries: everything appended to a nonempty `cur` was checked against `p` at
append time. -/
theorem go_tail_false {α : Type _} (p : α → Bool) :
    ∀ (xs cur : List α) (acc : List (List α)),
      (∀ g ∈ acc, ∀ z ∈ g.tail, p z = false) →
      (∀ z ∈ cur.reverse.tail, p z = false) →
      ∀ g ∈ partitionWhenTR.go p xs cur acc, ∀ z ∈ g.tail, p z = false := by
  intro xs
  induction xs with
  | nil =>
    intro cur acc hacc hcur
    unfold partitionWhenTR.go
    split
    · intro g hg
      exact hacc g (mem_reverse.mp hg)
    · intro g hg
      rw [mem_reverse, mem_cons] at hg
      rcases hg with rfl | hg
      · exact hcur
      · exact hacc g hg
  | cons x xs ih =>
    intro cur acc hacc hcur
    unfold partitionWhenTR.go
    split
    · rename_i h
      apply ih
      · intro g hg
        rcases mem_cons.mp hg with rfl | hg
        · exact hcur
        · exact hacc g hg
      · simp
    · rename_i h
      apply ih
      · exact hacc
      · cases cur with
        | nil => simp
        | cons c0 crest =>
          have hne : (c0 :: crest : List α) ≠ [] := by simp
          have hpx : p x = false := by
            have h2 : ¬ (p x && !(c0 :: crest).isEmpty) = true := h
            simp at h2
            simpa using h2
          rw [List.reverse_cons, List.tail_append_of_ne_nil (by simp)]
          intro z hz
          rcases mem_append.mp hz with hz | hz
          · exact hcur z hz
          · simp at hz; subst hz; exact hpx

theorem head?_append_left {α : Type _} (l l' : List α) (h : l ≠ []) : (l ++ l').head? = l.head? := by
  cases l with
  | nil => simp at h
  | cons a l => simp

/-- The hardest of the four: needs a loop invariant tracking not just what
`acc`/`cur` currently look like, but which *one* group in the eventual result
is exempt from `head_true` (the very first group of the whole list, which is
unconstrained). That exemption sits at `acc`'s own deepest/oldest element —
i.e. everything in `acc` *except* `acc.dropLast` needs `head_true` — until
the very first flush happens, tracked here by `cur = [] → acc = []` (`cur`
only starts `[]` at the top-level call; every state reachable after that has
`cur` nonempty, so the hypothesis becomes trivially true forever after). -/
theorem go_head_true {α : Type _} (p : α → Bool) :
    ∀ (xs cur : List α) (acc : List (List α)),
      (∀ g ∈ acc.dropLast, ∀ z, g.head? = some z → p z = true) →
      (acc ≠ [] → ∀ z, cur.reverse.head? = some z → p z = true) →
      (cur = [] → acc = []) →
      ∀ g ∈ (partitionWhenTR.go p xs cur acc).tail, ∀ z, g.head? = some z → p z = true := by
  intro xs
  induction xs with
  | nil =>
    intro cur acc hacc hcur hcoup
    unfold partitionWhenTR.go
    split
    · rw [tail_reverse]
      intro g hg
      exact hacc g (mem_reverse.mp hg)
    · rename_i hce
      have hcurne : cur ≠ [] := by simpa using hce
      cases hacc0 : acc with
      | nil => simp [reverse_cons]
      | cons a0 arest =>
        have haene : (a0 :: arest : List (List α)) ≠ [] := by simp
        rw [reverse_cons, tail_append_of_ne_nil (by simp), ← hacc0, tail_reverse]
        intro g hg
        rcases mem_append.mp hg with hg | hg
        · exact hacc g (mem_reverse.mp hg)
        · simp at hg; subst hg; exact hcur (hacc0 ▸ haene)
  | cons x xs ih =>
    intro cur acc hacc hcur hcoup
    unfold partitionWhenTR.go
    split
    · rename_i h
      have hpx : p x = true := (Bool.and_eq_true .. |>.mp h).1
      apply ih
      · cases hacc0 : acc with
        | nil => simp
        | cons a0 arest =>
          have haene : (a0 :: arest : List (List α)) ≠ [] := by simp
          rw [dropLast_cons_of_ne_nil haene]
          intro g hg
          rcases mem_cons.mp hg with rfl | hg
          · exact hcur (hacc0 ▸ haene)
          · exact hacc g (hacc0 ▸ hg)
      · intro _ z hz
        simp only [reverse_cons, reverse_nil, nil_append, head?_cons] at hz
        cases hz
        exact hpx
      · simp
    · rename_i h
      apply ih
      · exact hacc
      · intro haccne z hz
        cases hcurcase : cur with
        | nil => exact absurd (hcoup hcurcase) haccne
        | cons c0 crest =>
          rw [hcurcase, reverse_cons] at hz
          rw [head?_append_left _ _ (by simp)] at hz
          rw [← hcurcase] at hz
          exact hcur haccne z hz
      · intro he
        cases cur with
        | nil => simp at he
        | cons c0 crest => simp at he

theorem partitionWhenTR_flatten {α : Type _} (p : α → Bool) (xs : List α) :
    (partitionWhenTR p xs).flatten = xs := by
  simp only [partitionWhenTR]
  simpa using go_flatten p xs [] []

theorem partitionWhenTR_ne_nil_of_mem {α : Type _} (p : α → Bool) (xs : List α) :
    ∀ g ∈ partitionWhenTR p xs, g ≠ [] := by
  simp only [partitionWhenTR]
  exact go_ne_nil_of_mem p xs [] [] (by simp)

theorem partitionWhenTR_tail_false {α : Type _} (p : α → Bool) (xs : List α) :
    ∀ g ∈ partitionWhenTR p xs, ∀ z ∈ g.tail, p z = false := by
  simp only [partitionWhenTR]
  exact go_tail_false p xs [] [] (by simp) (by simp)

theorem partitionWhenTR_head_true {α : Type _} (p : α → Bool) (xs : List α) :
    ∀ g ∈ (partitionWhenTR p xs).tail, ∀ z, g.head? = some z → p z = true := by
  simp only [partitionWhenTR]
  exact go_head_true p xs [] [] (by simp) (by simp) (by simp)

theorem partitionWhenTR_eq_partitionWhen {α : Type _} (p : α → Bool) (xs : List α) :
    partitionWhenTR p xs = partitionWhen p xs :=
  partitionWhen_unique p xs (partitionWhenTR p xs)
    (partitionWhenTR_flatten p xs)
    (partitionWhenTR_ne_nil_of_mem p xs)
    (partitionWhenTR_tail_false p xs)
    (partitionWhenTR_head_true p xs)

/-! ### Equivalence of `partitionWhenFold` to `partitionWhen`

`partitionWhenFold` runs the *exact same* accumulator algorithm as
`partitionWhenTR` — same decision (`p x && !cur.isEmpty`), same two
transitions — just via `List.foldl` instead of a hand-written loop. So unlike
`partitionWhenTR` (which needed the full loop-invariant treatment above),
`partitionWhenFold` gets to reuse that work entirely: prove the two
accumulator computations produce the same thing (a same-shape comparison,
cheap like `partitionWhenSpan`/`partitionWhenTake`'s), then get equality to
`partitionWhen` for free by transitivity. -/

/-- `partitionWhenFold`'s inner `foldl` lambda, pulled out as its own
top-level function so it can be named in the statement of `go_eq_post_foldl`
below (the anonymous `let`-destructuring lambda in `partitionWhenFold` itself
can't be referred to from outside its definition). -/
private def stepFn {α : Type _} (p : α → Bool) :
    List (List α) × List α → α → List (List α) × List α
  | (groups, cur), x => if p x && !cur.isEmpty then (cur.reverse :: groups, [x]) else (groups, x :: cur)

/-- `partitionWhenFold`'s post-loop cleanup, pulled out for the same reason
as `stepFn`. -/
private def post {α : Type _} : List (List α) × List α → List (List α)
  | (groups, cur) => (if cur.isEmpty then groups else cur.reverse :: groups).reverse

theorem go_eq_post_foldl {α : Type _} (p : α → Bool) :
    ∀ (xs : List α) (groups : List (List α)) (cur : List α),
      partitionWhenTR.go p xs cur groups = post (xs.foldl (stepFn p) (groups, cur)) := by
  intro xs
  induction xs with
  | nil =>
    intro groups cur
    simp only [foldl_nil, post, partitionWhenTR.go]
    split <;> rfl
  | cons x xs ih =>
    intro groups cur
    simp only [foldl_cons, stepFn]
    unfold partitionWhenTR.go
    split
    · exact ih (cur.reverse :: groups) [x]
    · exact ih groups (x :: cur)

theorem partitionWhenFold_eq_partitionWhenTR {α : Type _} (p : α → Bool) (xs : List α) :
    partitionWhenFold p xs = partitionWhenTR p xs := by
  show post (xs.foldl (stepFn p) ([], [])) = partitionWhenTR.go p xs [] []
  exact (go_eq_post_foldl p xs [] []).symm

theorem partitionWhenFold_eq_partitionWhen {α : Type _} (p : α → Bool) (xs : List α) :
    partitionWhenFold p xs = partitionWhen p xs :=
  (partitionWhenFold_eq_partitionWhenTR p xs).trans (partitionWhenTR_eq_partitionWhen p xs)

theorem partitionWhenTake_flatten {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), (partitionWhenTake p xs).flatten = xs := by
  intro xs
  induction xs using partitionWhenTake.induct (p := p) with
  | case1 => simp [partitionWhenTake]
  | case2 x t ys ih =>
    simp only [partitionWhenTake, flatten_cons, cons_append]
    rw [show ys = t.dropWhile (!p ·) from rfl] at ih
    rw [ih, takeWhile_append_dropWhile]

theorem partitionWhenTake_ne_nil_of_mem {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), ∀ g ∈ partitionWhenTake p xs, g ≠ [] := by
  intro xs
  induction xs using partitionWhenTake.induct (p := p) with
  | case1 => simp [partitionWhenTake]
  | case2 x t ys ih =>
    rw [show ys = t.dropWhile (!p ·) from rfl] at ih
    simp only [partitionWhenTake]
    intro h hmem
    rcases mem_cons.mp hmem with rfl | hmem
    · simp
    · exact ih h hmem

theorem partitionWhenTake_tail_false {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), ∀ g ∈ partitionWhenTake p xs, ∀ z ∈ g.tail, p z = false := by
  intro xs
  induction xs using partitionWhenTake.induct (p := p) with
  | case1 => simp [partitionWhenTake]
  | case2 x t ys ih =>
    rw [show ys = t.dropWhile (!p ·) from rfl] at ih
    simp only [partitionWhenTake]
    intro h hmem
    rcases mem_cons.mp hmem with rfl | hmem
    · simp only [tail_cons]
      intro z hz
      have := List.all_takeWhile (p := (!p ·)) (l := t)
      rw [List.all_eq_true] at this
      simpa using this z hz
    · exact ih h hmem

theorem partitionWhenTake_head_true {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), ∀ g ∈ (partitionWhenTake p xs).tail, ∀ z, g.head? = some z → p z = true := by
  intro xs
  induction xs using partitionWhenTake.induct (p := p) with
  | case1 => simp [partitionWhenTake]
  | case2 x t ysdrop ih =>
    rw [show ysdrop = t.dropWhile (!p ·) from rfl] at ih
    simp only [partitionWhenTake, tail_cons]
    cases hdrop : t.dropWhile (!p ·) with
    | nil => simp [partitionWhenTake]
    | cons y ys =>
      rw [hdrop] at ih
      simp only [partitionWhenTake, tail_cons] at ih
      simp only [partitionWhenTake]
      intro h hmem z hz
      rcases mem_cons.mp hmem with rfl | hmem
      · simp only [head?_cons, Option.some.injEq] at hz
        subst hz
        have hne := head?_dropWhile_not (!p ·) t
        rw [hdrop] at hne
        simpa using hne
      · exact ih h hmem z hz

theorem partitionWhenTake_eq_partitionWhen {α : Type _} (p : α → Bool) (xs : List α) :
    partitionWhenTake p xs = partitionWhen p xs :=
  partitionWhen_unique p xs (partitionWhenTake p xs)
    (partitionWhenTake_flatten p xs)
    (partitionWhenTake_ne_nil_of_mem p xs)
    (partitionWhenTake_tail_false p xs)
    (partitionWhenTake_head_true p xs)

/-- `partitionWhenSpan` isn't proven equal to `partitionWhen` via the
spec (unlike `partitionWhenTake`) — it doesn't need to be. Its recursion has
the *same shape* as `partitionWhenTake`'s (advance by one whole group per
step, via whatever computes the split), so once `span` is known to compute
the same split as `takeWhile`/`dropWhile`, a direct induction shows the two
functions equal outright, and equality to `partitionWhen` follows
by transitivity through the proof already done for `partitionWhenTake`.
Core has no `span = (takeWhile, dropWhile)` lemma (mirroring the missing
`span` length lemma needed for `partitionWhenSpan`'s termination proof), so
this bridge is proved the same way: unfolding `span`'s `loop` and
generalizing the accumulator. -/
private theorem span_loop_eq {α : Type _} (q : α → Bool) :
    ∀ (l acc : List α), List.span.loop q l acc = (acc.reverse ++ l.takeWhile q, l.dropWhile q)
  | [], acc => by simp [List.span.loop]
  | a :: l, acc => by
    unfold List.span.loop
    cases hqa : q a with
    | true =>
      rw [span_loop_eq q l (a :: acc)]
      have h1 : (a :: l).takeWhile q = a :: l.takeWhile q := takeWhile_cons_of_pos hqa
      have h2 : (a :: l).dropWhile q = l.dropWhile q := dropWhile_cons_of_pos hqa
      simp [h1, h2]
    | false =>
      have hnq : ¬ q a = true := by simp [hqa]
      have h1 : (a :: l).takeWhile q = [] := takeWhile_cons_of_neg hnq
      have h2 : (a :: l).dropWhile q = a :: l := dropWhile_cons_of_neg hnq
      simp [h1, h2]

theorem span_eq_takeWhile_dropWhile {α : Type _} (q : α → Bool) (l : List α) :
    l.span q = (l.takeWhile q, l.dropWhile q) := by
  simpa [List.span] using span_loop_eq q l []

theorem partitionWhenSpan_eq_partitionWhenTake {α : Type _} (p : α → Bool) :
    ∀ (xs : List α), partitionWhenSpan p xs = partitionWhenTake p xs := by
  intro xs
  induction xs using partitionWhenSpan.induct (p := p) with
  | case1 => simp [partitionWhenSpan, partitionWhenTake]
  | case2 h t xys ih =>
    have hspan := span_eq_takeWhile_dropWhile (!p ·) t
    have hxys : xys = (t.takeWhile (!p ·), t.dropWhile (!p ·)) := by
      rw [show xys = t.span (!p ·) from rfl, hspan]
    rw [hxys] at ih
    simp only [partitionWhenSpan, partitionWhenTake, hspan]
    rw [ih]

theorem partitionWhenSpan_eq_partitionWhen {α : Type _} (p : α → Bool) (xs : List α) :
    partitionWhenSpan p xs = partitionWhen p xs :=
  (partitionWhenSpan_eq_partitionWhenTake p xs).trans (partitionWhenTake_eq_partitionWhen p xs)

end List
