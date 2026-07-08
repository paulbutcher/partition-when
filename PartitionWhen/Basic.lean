namespace List

/-- Partition a list into sublists, starting a new sublist each time `p`
returns `true` (the triggering element becomes the first element of the new
sublist). The very first element never starts an empty leading sublist. -/
def partitionWhen {α : Type _} (p : α → Bool) : List α → List (List α)
  | [] => []
  | [x] => [[x]]
  | x :: y :: rest =>
    match partitionWhen p (y :: rest) with
    | g :: gs => if p y then [x] :: g :: gs else (x :: g) :: gs
    | [] => [[x]]

/-- Tail-recursive version of `partitionWhen`. `partitionWhen` decides
whether an element starts a new group by looking at the *result* of
recursing on the rest of the list first, which means it does work after its
recursive call and so isn't a tail call. Here the same decision (does the
upcoming element trigger a new group?) is instead made the moment an element
is consumed, walking left to right with an explicit accumulator: `cur` is the
group being built (in reverse, since we only ever prepend to it) and `acc` is
the list of already-finished groups (also in reverse). Every recursive call
to `go` is then in tail position, and the two `reverse`s only happen once
each, at the very end. -/
def partitionWhenTR {α : Type _} (p : α → Bool) (xs : List α) : List (List α) :=
  go xs [] []
where
  go : List α → List α → List (List α) → List (List α)
    | [], cur, acc => if cur.isEmpty then acc.reverse else (cur.reverse :: acc).reverse
    | x :: xs, cur, acc =>
      if p x && !cur.isEmpty then
        go xs [x] (cur.reverse :: acc)
      else
        go xs (x :: cur) acc

/-- Same semantics as `partitionWhen`, implemented via `List.foldl` instead
of plain recursion. -/
def partitionWhenFold {α : Type _} (p : α → Bool) (xs : List α) : List (List α) :=
  let (groups, cur) := xs.foldl
    (fun (acc : List (List α) × List α) x =>
      let (groups, cur) := acc
      if p x && !cur.isEmpty then
        (cur.reverse :: groups, [x])
      else
        (groups, x :: cur))
    ([], [])
  (if cur.isEmpty then groups else cur.reverse :: groups).reverse

/-- Same semantics as `partitionWhen`, implemented by repeatedly peeling a
group off the front with `takeWhile` / `dropWhile` instead of folding. -/
def partitionWhenTake {α : Type _} (p : α → Bool) : List α → List (List α)
  | [] => []
  | h :: t =>
    let xs := t.takeWhile (!p ·)
    let ys := t.dropWhile (!p ·)
    (h :: xs) :: partitionWhenTake p ys
termination_by t => t.length
decreasing_by
  simp_wf
  have := (List.dropWhile_sublist (!p ·) (l := t)).length_le
  omega

/-- `List.span` has no pre-existing length lemma in core, so this proves
`(l.span q).snd.length ≤ l.length` (needed for `partitionWhenSpan`'s
termination proof) by unfolding `span`'s tail-recursive `loop`. -/
private theorem span_loop_snd_length_le {α : Type _} (q : α → Bool) :
    ∀ (l acc : List α), (List.span.loop q l acc).snd.length ≤ l.length
  | [], acc => by simp [List.span.loop]
  | a :: l, acc => by
    unfold List.span.loop
    cases q a with
    | true =>
      have ih := span_loop_snd_length_le q l (a :: acc)
      simp only [List.length_cons]
      omega
    | false => simp

theorem span_snd_length_le {α : Type _} (q : α → Bool) (l : List α) :
    (l.span q).snd.length ≤ l.length := by
  simpa [List.span] using span_loop_snd_length_le q l []

/-- Same semantics as `partitionWhen`, implemented with a single pass per
group via `span` instead of the separate `takeWhile` / `dropWhile` traversals
used by `partitionWhenTake`. -/
def partitionWhenSpan {α : Type _} (p : α → Bool) : List α → List (List α)
  | [] => []
  | h :: t =>
    let xys := t.span (!p ·)
    (h :: xys.1) :: partitionWhenSpan p xys.2
termination_by t => t.length
decreasing_by
  simp_wf
  have hle := span_snd_length_le (!p ·) t
  omega

end List
