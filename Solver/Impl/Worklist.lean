-- Copyright (c) 2026 Martin Rinard
import Solver.Impl.Engine

/-!
# `Solver.Impl.Worklist` — efficient Kildall worklist, by refinement

The executable
**Kildall worklist** — only re-evaluate nodes whose inputs changed — proven to compute the *same*
result as the naive Kleene engine (`solveWL{Must,May} = solve{Must,May}`), so every downstream
correctness/optimality theorem transfers by rewrite, re-proving nothing. Generic extremality
(`solveMust_extremal_of_postfix`/`solveMay_extremal_of_prefix`) is the reusable core the generator
appeals to per ghost.

## Efficiency techniques (the algorithm must actually be fast)
- **Empty-queue termination** (`wlRun` stops when `queue = []`, `O(1)`), NOT `iterToFix`'s `O(N)`-per-step
  `F x = x` equality. Fuel is a *bound* only.
- **Precomputed reader adjacency** `Array (List Node)`, `O(1)` lookup in the hot loop.
- **`O(1)` `Array.set!`** fact updates; facts are bitvectors (`ESet = BitVec n`, `O(n/w)` meet/compare).
- **Worklist = list-stack**, `O(1)` push/pop.

The per-`g` locality lemmas (`hloc`) and the per-ghost transfers are NOT here — they are the content
the generator emits per ghost; this module is the generic, ghost-agnostic engine.
-/

namespace Solver

open BaseLanguage Tac Semantics

variable {n : Nat}

/-! ## Executable worklist state and step -/

structure WL (n : Nat) where
  arr   : Array (ESet n)
  queue : List Node
deriving DecidableEq

/-- One worklist step: pop `nd`; recompute its fact; if unchanged, just drop it; otherwise write back
    (`O(1)` `set!`) and enqueue its readers. `readers[nd]` are the nodes whose `g` reads index `nd`. -/
def wlStep (g : Array (ESet n) → Node → ESet n) (combine : ESet n → ESet n → ESet n)
    (readers : Array (List Node)) : WL n → WL n
  | ⟨arr, []⟩      => ⟨arr, []⟩
  | ⟨arr, nd :: q⟩ =>
    let new := combine (gA arr nd) (g arr nd)
    if new = gA arr nd then ⟨arr, q⟩
    else ⟨arr.set! nd new, (readers[nd]?.getD []) ++ q⟩

/-- Fuel-threaded driver that halts as soon as the queue is **empty** (the `O(1)` termination test). -/
def wlRun (step : WL n → WL n) : Nat → WL n → WL n
  | 0,    s => s
  | k+1,  s => match s.queue with
    | []     => s
    | _ :: _ => wlRun step k (step s)

/-! ## Engine knobs and the fuel bound -/

/-- Precompute the reader adjacency `readers[nd] = deps P nd` (built once, `O(1)` lookup thereafter). -/
def readersOf (P : Program) (deps : Program → Node → List Node) : Array (List Node) :=
  Array.ofFn (n := P.size) (fun nd => deps P nd.val)

/-- A loose upper bound on any single node's reader count: the total reader-edge count. -/
def degBound (P : Program) (deps : Program → Node → List Node) : Nat :=
  sumN ((List.range P.size).map (fun nd => (deps P nd).length))

/-- The single decreasing measure for termination: `measure · (1 + degBound) + |queue|`. -/
def wlMeas (P : Program) (measure : Program → Array (ESet n) → Nat)
    (deps : Program → Node → List Node) (s : WL n) : Nat :=
  measure P s.arr * (1 + degBound P deps) + s.queue.length

/-- Initial worklist state: seed array, all nodes pending. -/
def wlInit (P : Program) (seed : Array (ESet n)) : WL n := ⟨seed, List.range P.size⟩

/-- The executable worklist solve. Precomputes the reader adjacency, then runs to an empty queue with
    fuel `wlMeas init + 1` (a provable upper bound; the loop halts earlier on empty queue). -/
def solveWL (P : Program) (g : Array (ESet n) → Node → ESet n)
    (deps : Program → Node → List Node) (combine : ESet n → ESet n → ESet n)
    (measure : Program → Array (ESet n) → Nat) (seed : Array (ESet n)) : Array (ESet n) :=
  let readers := readersOf P deps
  (wlRun (wlStep g combine readers)
      (wlMeas P measure deps (wlInit P seed) + 1) (wlInit P seed)).arr

/-! ## The two solves as instantiations of the one engine -/

/-- Worklist must-solve (avail / anti / postp): `&&&`, `topSeed`, `measM`. -/
def solveWLMust (P : Program) (g : Array (ESet n) → Node → ESet n)
    (deps : Program → Node → List Node) : Array (ESet n) :=
  solveWL P g deps (· &&& ·) measM (topSeed P)

/-- Worklist may-solve (used): `|||`, `botSeed`, `measV`. -/
def solveWLMay (P : Program) (g : Array (ESet n) → Node → ESet n)
    (deps : Program → Node → List Node) : Array (ESet n) :=
  solveWL P g deps (· ||| ·) measV (botSeed P)

/-! ## Array `set!` plumbing -/

theorem set!_size (a : Array (ESet n)) (i : Nat) (v : ESet n) : (a.set! i v).size = a.size := by
  simp [Array.set!, Array.size_setIfInBounds]

/-- Reading the written index back (in range): `gA (a.set! i v) i = v`. -/
theorem gA_set_eq {a : Array (ESet n)} {i : Nat} {v : ESet n} (h : i < a.size) :
    gA (a.set! i v) i = v := by
  unfold gA Array.set!
  simp [h]

/-- Reading a different index is unaffected by the write. -/
theorem gA_set_ne {a : Array (ESet n)} {i j : Nat} {v : ESet n} (h : j ≠ i) :
    gA (a.set! i v) j = gA a j := by
  unfold gA Array.set!
  rw [Array.getElem?_setIfInBounds, if_neg (fun hc : i = j => h hc.symm)]

/-! ## Termination: the worklist drains -/

theorem wlStep_cons_noop {g : Array (ESet n) → Node → ESet n} {combine}
    {readers : Array (List Node)} {arr : Array (ESet n)} {nd : Node} {q : List Node}
    (h : combine (gA arr nd) (g arr nd) = gA arr nd) :
    wlStep g combine readers ⟨arr, nd :: q⟩ = ⟨arr, q⟩ := by
  simp only [wlStep]; rw [if_pos h]

theorem wlStep_cons_change {g : Array (ESet n) → Node → ESet n} {combine}
    {readers : Array (List Node)} {arr : Array (ESet n)} {nd : Node} {q : List Node}
    (h : combine (gA arr nd) (g arr nd) ≠ gA arr nd) :
    wlStep g combine readers ⟨arr, nd :: q⟩
      = ⟨arr.set! nd (combine (gA arr nd) (g arr nd)), (readers[nd]?.getD []) ++ q⟩ := by
  simp only [wlStep]; rw [if_neg h]

/-- A list member is ≤ the summed `f`-image (used to bound a node's reader count by `degBound`). -/
theorem le_sumN_map {α} (f : α → Nat) {x : α} :
    ∀ {xs : List α}, x ∈ xs → f x ≤ sumN (xs.map f)
  | [], hx => by simp at hx
  | y :: ys, hx => by
      simp only [List.map_cons, sumN, List.foldr_cons]
      rcases List.mem_cons.mp hx with h | h
      · subst h; exact Nat.le_add_right _ _
      · exact Nat.le_trans (le_sumN_map f h) (Nat.le_add_left _ _)

/-- `readersOf` is read in range as `deps P nd`. -/
theorem readersOf_get {P : Program} {deps : Program → Node → List Node} {nd : Node}
    (h : nd < P.size) : (readersOf P deps)[nd]?.getD ([] : List Node) = deps P nd := by
  unfold readersOf
  have hsz : nd < (Array.ofFn (n := P.size) (fun nd => deps P nd.val)).size := by
    rw [Array.size_ofFn]; exact h
  rw [Array.getElem?_eq_getElem hsz, Array.getElem_ofFn]
  rfl

/-- Out of range the precomputed reader list is empty. -/
theorem readersOf_get_oob {P : Program} {deps : Program → Node → List Node} {nd : Node}
    (h : ¬ nd < P.size) : (readersOf P deps)[nd]?.getD ([] : List Node) = [] := by
  have : ¬ nd < (readersOf P deps).size := by unfold readersOf; rw [Array.size_ofFn]; exact h
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt this)]
  rfl

/-- Any single node's precomputed reader count is ≤ `degBound`. -/
theorem readers_len_le_degBound {P : Program} {deps : Program → Node → List Node} (nd : Node) :
    ((readersOf P deps)[nd]?.getD ([] : List Node)).length ≤ degBound P deps := by
  by_cases h : nd < P.size
  · rw [readersOf_get h]
    exact le_sumN_map (fun m => (deps P m).length) (List.mem_range.mpr h)
  · rw [readersOf_get_oob h]; simp

/-- Generic, invariant-aware termination for `wlRun`. -/
theorem wlRun_queue_nil (step : WL n → WL n) (Inv : WL n → Prop) (Φ : WL n → Nat)
    (hpres : ∀ s, Inv s → Inv (step s))
    (hdec : ∀ s, Inv s → s.queue ≠ [] → Φ (step s) < Φ s) :
    ∀ (fuel : Nat) (s : WL n), Inv s → Φ s < fuel → (wlRun step fuel s).queue = [] := by
  intro fuel
  induction fuel with
  | zero => intro s _ hs; exact absurd hs (Nat.not_lt_zero _)
  | succ k ih =>
      intro s hInv hs
      obtain ⟨arr, q⟩ := s
      cases q with
      | nil => rfl
      | cons a q' =>
          show (wlRun step k (step ⟨arr, a :: q'⟩)).queue = []
          have hne : (⟨arr, a :: q'⟩ : WL n).queue ≠ [] := by simp
          have hd := hdec ⟨arr, a :: q'⟩ hInv hne
          exact ih (step ⟨arr, a :: q'⟩) (hpres _ hInv) (by omega)

/-- The worklist invariant: size is `P.size` and every queued node is in range. -/
def WLInv (P : Program) (s : WL n) : Prop :=
  s.arr.size = P.size ∧ (∀ m ∈ s.queue, m < P.size)

/-- `wlStep` preserves `WLInv` provided every reader list stays in range. -/
theorem wlStep_WLInv {P : Program} {g combine} {deps : Program → Node → List Node}
    (hdeps : ∀ (nd : Node), ∀ m ∈ (readersOf P deps)[nd]?.getD ([] : List Node), m < P.size)
    {s : WL n} (hInv : WLInv P s) :
    WLInv P (wlStep g combine (readersOf P deps) s) := by
  obtain ⟨arr, q⟩ := s
  obtain ⟨hsz, hrange⟩ := hInv
  cases q with
  | nil => exact ⟨hsz, hrange⟩
  | cons nd q' =>
      by_cases hch : combine (gA arr nd) (g arr nd) = gA arr nd
      · rw [wlStep_cons_noop hch]
        exact ⟨hsz, fun m hm => hrange m (List.mem_cons_of_mem nd hm)⟩
      · rw [wlStep_cons_change hch]
        refine ⟨by rw [set!_size]; exact hsz, ?_⟩
        intro m hm
        rcases List.mem_append.mp hm with h | h
        · exact hdeps nd m h
        · exact hrange m (List.mem_cons_of_mem nd h)

/-- The reader-range hypothesis holds for `succList` under `WellFormed`. -/
theorem succList_in_range {P : Program} (hwf : WellFormed P) (nd : Node) :
    ∀ m ∈ (readersOf P succList)[nd]?.getD ([] : List Node), m < P.size := by
  by_cases h : nd < P.size
  · rw [readersOf_get h]
    intro m hm
    obtain ⟨instr, hf, hmem⟩ := mem_succList hm
    exact hwf.succ_lt hf hmem
  · rw [readersOf_get_oob h]; simp

/-- The reader-range hypothesis holds for `predList` (predecessors are always in range). -/
theorem predList_in_range {P : Program} (nd : Node) :
    ∀ m ∈ (readersOf P predList)[nd]?.getD ([] : List Node), m < P.size := by
  by_cases h : nd < P.size
  · rw [readersOf_get h]
    intro m hm
    exact (mem_predList.mp hm).1
  · rw [readersOf_get_oob h]; simp

/-- A non-empty successor list forces its source node in range (out of range `fetch` is `none`). -/
theorem succList_mem_lt {P : Program} {m s : Node} (hs : s ∈ succList P m) : m < P.size := by
  obtain ⟨instr, hf, _⟩ := mem_succList hs
  exact fetch_lt hf

/-- **The measure-decrease lemma.** `Φ = wlMeas` strictly drops on every non-empty-queue `wlStep`. -/
theorem wlStep_meas_lt {P : Program} {g combine} {deps : Program → Node → List Node}
    {measure : Program → Array (ESet n) → Nat}
    (hdrop : ∀ arr nd, nd < P.size → arr.size = P.size →
        combine (gA arr nd) (g arr nd) ≠ gA arr nd →
        measure P (arr.set! nd (combine (gA arr nd) (g arr nd))) < measure P arr)
    {s : WL n} (hInv : WLInv P s) (hne : s.queue ≠ []) :
    wlMeas P measure deps (wlStep g combine (readersOf P deps) s)
      < wlMeas P measure deps s := by
  obtain ⟨arr, q⟩ := s
  obtain ⟨hsz, hrange⟩ := hInv
  cases q with
  | nil => exact absurd rfl hne
  | cons nd q' =>
      have hndlt : nd < P.size := hrange nd (by simp)
      by_cases hch : combine (gA arr nd) (g arr nd) = gA arr nd
      · rw [wlStep_cons_noop hch]
        simp only [wlMeas, List.length_cons]
        omega
      · rw [wlStep_cons_change hch]
        have hmd : measure P (arr.set! nd (combine (gA arr nd) (g arr nd))) < measure P arr :=
          hdrop arr nd hndlt hsz hch
        have hbound : ((readersOf P deps)[nd]?.getD ([] : List Node)).length ≤ degBound P deps :=
          readers_len_le_degBound nd
        have hkey : measure P (arr.set! nd (combine (gA arr nd) (g arr nd))) * (1 + degBound P deps)
              + (1 + degBound P deps) ≤ measure P arr * (1 + degBound P deps) := by
          have h1 : (measure P (arr.set! nd (combine (gA arr nd) (g arr nd))) + 1)
                * (1 + degBound P deps) ≤ measure P arr * (1 + degBound P deps) :=
            Nat.mul_le_mul_right _ (by omega)
          rwa [Nat.add_mul, Nat.one_mul] at h1
        simp only [wlMeas, List.length_append, List.length_cons]
        generalize hP1 : measure P (arr.set! nd (combine (gA arr nd) (g arr nd)))
            * (1 + degBound P deps) = P1 at hkey ⊢
        generalize hP2 : measure P arr * (1 + degBound P deps) = P2 at hkey ⊢
        omega

/-- The termination deliverable: the worklist queue is empty in the produced state. -/
theorem solveWL_queue_nil {P : Program} {g combine} {deps : Program → Node → List Node}
    {measure : Program → Array (ESet n) → Nat} {seed : Array (ESet n)}
    (hseed : seed.size = P.size)
    (hdeps : ∀ (nd : Node), ∀ m ∈ (readersOf P deps)[nd]?.getD ([] : List Node), m < P.size)
    (hdrop : ∀ arr nd, nd < P.size → arr.size = P.size →
        combine (gA arr nd) (g arr nd) ≠ gA arr nd →
        measure P (arr.set! nd (combine (gA arr nd) (g arr nd))) < measure P arr) :
    (wlRun (wlStep g combine (readersOf P deps))
      (wlMeas P measure deps (wlInit P seed) + 1) (wlInit P seed)).queue = [] := by
  apply wlRun_queue_nil (wlStep g combine (readersOf P deps)) (WLInv P)
    (wlMeas P measure deps)
    (fun s hs => wlStep_WLInv hdeps hs)
    (fun s hs hne => wlStep_meas_lt hdrop hs hne)
  · exact ⟨hseed, fun m hm => List.mem_range.mp hm⟩
  · exact Nat.lt_succ_self _

/-! ## Consistency invariant ⇒ the worklist result is a `combine`-step fixpoint -/

/-- Every off-queue, in-range node is locally settled. -/
def Consistent (P : Program) (g : Array (ESet n) → Node → ESet n)
    (combine : ESet n → ESet n → ESet n) (s : WL n) : Prop :=
  ∀ m, m < P.size → m ∉ s.queue → gA s.arr m = combine (gA s.arr m) (g s.arr m)

/-- Initially vacuous: the queue is every node, so no in-range node is off-queue. -/
theorem Consistent_init {P : Program} {g combine} (seed : Array (ESet n)) :
    Consistent P g combine (wlInit P seed) := by
  intro m hm hmq
  exact absurd (List.mem_range.mpr hm) hmq

/-- **The consistency-preservation lemma.** Popping `nd` and enqueuing its readers re-covers every node
    whose local settledness `nd`'s write could disturb. -/
theorem wlStep_consistent {P : Program} {g combine} {deps : Program → Node → List Node}
    (hloc : ∀ (arr : Array (ESet n)) (nd : Node) (v : ESet n) (m : Node),
        m ∉ deps P nd → g (arr.set! nd v) m = g arr m)
    (hidem : ∀ a b : ESet n, combine (combine a b) b = combine a b)
    {s : WL n} (hwl : WLInv P s) (hc : Consistent P g combine s) :
    Consistent P g combine (wlStep g combine (readersOf P deps) s) := by
  obtain ⟨arr, q⟩ := s
  obtain ⟨hsz, hrange⟩ := hwl
  cases q with
  | nil => exact hc
  | cons nd q' =>
      have hndlt : nd < P.size := hrange nd (by simp)
      have hndarr : nd < arr.size := by rw [hsz]; exact hndlt
      by_cases hch : combine (gA arr nd) (g arr nd) = gA arr nd
      · rw [wlStep_cons_noop hch]
        intro m hm hmq'
        by_cases hmnd : m = nd
        · subst hmnd; exact hch.symm
        · exact hc m hm (by simp only [List.mem_cons, not_or]; exact ⟨hmnd, hmq'⟩)
      · rw [wlStep_cons_change hch]
        intro m hm hmq
        simp only [List.mem_append, not_or] at hmq
        obtain ⟨hmdeps, hmq'⟩ := hmq
        rw [readersOf_get hndlt] at hmdeps
        by_cases hmnd : m = nd
        · rw [hmnd] at hmdeps ⊢
          rw [gA_set_eq hndarr, hloc arr nd _ nd hmdeps]
          exact (hidem (gA arr nd) (g arr nd)).symm
        · rw [gA_set_ne hmnd, hloc arr nd _ m hmdeps]
          exact hc m hm (by simp only [List.mem_cons, not_or]; exact ⟨hmnd, hmq'⟩)

/-- Any invariant preserved by `step` survives `wlRun`. -/
theorem wlRun_invariant (step : WL n → WL n) (Inv : WL n → Prop)
    (hpres : ∀ s, Inv s → Inv (step s)) :
    ∀ (fuel : Nat) (s : WL n), Inv s → Inv (wlRun step fuel s) := by
  intro fuel
  induction fuel with
  | zero => intro s hs; exact hs
  | succ k ih =>
      intro s hs
      obtain ⟨arr, q⟩ := s
      cases q with
      | nil => exact hs
      | cons a q' =>
          show Inv (wlRun step k (step ⟨arr, a :: q'⟩))
          exact ih (step ⟨arr, a :: q'⟩) (hpres _ hs)

/-- The worklist result is settled at every node. -/
theorem solveWL_settled {P : Program} {g combine} {deps : Program → Node → List Node}
    {measure : Program → Array (ESet n) → Nat} {seed : Array (ESet n)}
    (hseed : seed.size = P.size)
    (hdeps : ∀ (nd : Node), ∀ m ∈ (readersOf P deps)[nd]?.getD ([] : List Node), m < P.size)
    (hdrop : ∀ arr nd, nd < P.size → arr.size = P.size →
        combine (gA arr nd) (g arr nd) ≠ gA arr nd →
        measure P (arr.set! nd (combine (gA arr nd) (g arr nd))) < measure P arr)
    (hloc : ∀ (arr : Array (ESet n)) (nd : Node) (v : ESet n) (m : Node),
        m ∉ deps P nd → g (arr.set! nd v) m = g arr m)
    (hidem : ∀ a b : ESet n, combine (combine a b) b = combine a b) :
    ∀ m, m < P.size →
      gA (solveWL P g deps combine measure seed) m
        = combine (gA (solveWL P g deps combine measure seed) m)
            (g (solveWL P g deps combine measure seed) m) := by
  intro m hm
  have hfinal := wlRun_invariant (wlStep g combine (readersOf P deps))
    (fun s => WLInv P s ∧ Consistent P g combine s)
    (fun s hs => ⟨wlStep_WLInv hdeps hs.1, wlStep_consistent hloc hidem hs.1 hs.2⟩)
    (wlMeas P measure deps (wlInit P seed) + 1) (wlInit P seed)
    ⟨⟨hseed, fun k hk => List.mem_range.mp hk⟩, Consistent_init seed⟩
  have hqnil := solveWL_queue_nil (g := g) (combine := combine) hseed hdeps hdrop
  show gA (wlRun (wlStep g combine (readersOf P deps))
      (wlMeas P measure deps (wlInit P seed) + 1) (wlInit P seed)).arr m = _
  exact hfinal.2 m hm (by rw [hqnil]; simp)

/-! ## Meet/join congruence (used by the generator's emitted per-`g` locality lemmas) -/

/-- Meet congruence: agreeing on every member ⇒ equal meets. -/
theorem meetList_congr {f f' : Node → ESet n} {xs : List Node}
    (h : ∀ x ∈ xs, f x = f' x) : meetList f xs = meetList f' xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [meetList]
      rw [h x (by simp), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- Join congruence: agreeing on every member ⇒ equal joins. -/
theorem joinList_congr {f f' : Node → ESet n} {xs : List Node}
    (h : ∀ x ∈ xs, f x = f' x) : joinList f xs = joinList f' xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [joinList]
      rw [h x (by simp), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-! ## Instantiation helpers (`combine`/measure-specific inputs) -/

theorem and_idem_right (a b : ESet n) : a &&& b &&& b = a &&& b := by
  rw [BitVec.and_assoc, BitVec.and_self]

theorem or_idem_right (a b : ESet n) : a ||| b ||| b = a ||| b := by
  rw [BitVec.or_assoc, BitVec.or_self]

/-- Single-index measure drop: lowering one node's fact below its current value strictly drops `measM`. -/
theorem measM_set_lt {P : Program} {arr : Array (ESet n)} {nd : Node} {v : ESet n}
    (hsz : arr.size = P.size) (hndlt : nd < P.size) (hsub : v.toNat < (gA arr nd).toNat) :
    measM P (arr.set! nd v) < measM P arr := by
  have hndarr : nd < arr.size := by rw [hsz]; exact hndlt
  unfold measM
  apply sumN_map_lt (List.range P.size)
    (fun m => (gA (arr.set! nd v) m).toNat) (fun m => (gA arr m).toNat)
    ?_ (List.mem_range.mpr hndlt) ?_
  · intro m _
    by_cases hmnd : m = nd
    · subst hmnd; rw [gA_set_eq hndarr]; exact Nat.le_of_lt hsub
    · rw [gA_set_ne hmnd]; exact Nat.le_refl _
  · rw [gA_set_eq hndarr]; exact hsub

/-- May dual: raising one node's fact above its current value strictly drops `measV`. -/
theorem measV_set_lt {P : Program} {arr : Array (ESet n)} {nd : Node} {v : ESet n}
    (hsz : arr.size = P.size) (hndlt : nd < P.size) (hsub : (~~~v).toNat < (~~~ gA arr nd).toNat) :
    measV P (arr.set! nd v) < measV P arr := by
  have hndarr : nd < arr.size := by rw [hsz]; exact hndlt
  unfold measV
  apply sumN_map_lt (List.range P.size)
    (fun m => (~~~ gA (arr.set! nd v) m).toNat) (fun m => (~~~ gA arr m).toNat)
    ?_ (List.mem_range.mpr hndlt) ?_
  · intro m _
    by_cases hmnd : m = nd
    · subst hmnd; rw [gA_set_eq hndarr]; exact Nat.le_of_lt hsub
    · rw [gA_set_ne hmnd]; exact Nat.le_refl _
  · rw [gA_set_eq hndarr]; exact hsub

/-- The must instantiation of `hdrop`: a genuine `&&&`-change strictly drops `measM`. -/
theorem must_hdrop {P : Program} {g : Array (ESet n) → Node → ESet n}
    (arr : Array (ESet n)) (nd : Node) (hndlt : nd < P.size) (hsz : arr.size = P.size)
    (hch : (gA arr nd &&& g arr nd) ≠ gA arr nd) :
    measM P (arr.set! nd (gA arr nd &&& g arr nd)) < measM P arr := by
  apply measM_set_lt hsz hndlt
  exact toNat_lt_of_le_ne (toNat_and_le _ _) hch

/-- The may instantiation of `hdrop`: a genuine `|||`-change strictly drops `measV`. -/
theorem may_hdrop {P : Program} {g : Array (ESet n) → Node → ESet n}
    (arr : Array (ESet n)) (nd : Node) (hndlt : nd < P.size) (hsz : arr.size = P.size)
    (hch : (gA arr nd ||| g arr nd) ≠ gA arr nd) :
    measV P (arr.set! nd (gA arr nd ||| g arr nd)) < measV P arr := by
  apply measV_set_lt hsz hndlt
  apply toNat_lt_of_le_ne
  · rw [BitVec.not_or]; exact toNat_and_le _ _
  · intro hcon
    apply hch
    have := congrArg (~~~ ·) hcon
    simpa [BitVec.not_not] using this

/-- The worklist result has the right length (`WLInv` is carried through `wlRun`). -/
theorem solveWL_size {P : Program} {g combine} {deps : Program → Node → List Node}
    {measure : Program → Array (ESet n) → Nat} {seed : Array (ESet n)}
    (hseed : seed.size = P.size)
    (hdeps : ∀ (nd : Node), ∀ m ∈ (readersOf P deps)[nd]?.getD ([] : List Node), m < P.size) :
    (solveWL P g deps combine measure seed).size = P.size := by
  have hinv := wlRun_invariant (wlStep g combine (readersOf P deps)) (WLInv P)
    (fun s hs => wlStep_WLInv hdeps hs)
    (wlMeas P measure deps (wlInit P seed) + 1) (wlInit P seed)
    ⟨hseed, fun k hk => List.mem_range.mp hk⟩
  exact hinv.1

/-! ## Refinement equality `solveWL{Must,May} = solve{Must,May}` -/

theorem incl_and_intro {t a b : ESet n} (ha : Incl t a) (hb : Incl t b) : Incl t (a &&& b) := by
  apply incl_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, Bool.and_eq_true]
  exact ⟨incl_iff.mp ha i hi, incl_iff.mp hb i hi⟩

theorem incl_or_elim {a b t : ESet n} (ha : Incl a t) (hb : Incl b t) : Incl (a ||| b) t := by
  apply incl_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_or, Bool.or_eq_true] at hi
  rcases hi with h | h
  · exact incl_iff.mp ha i h
  · exact incl_iff.mp hb i h

theorem incl_topV (t : ESet n) : Incl t (topV n) := by
  apply incl_iff.mpr
  intro i hi
  have : i < n := BitVec.lt_of_getLsbD hi
  simp [topV, this]

/-- `meetList` is monotone in its summands (shared worklist-step helper). -/
theorem meetList_mono {f g : Node → ESet n} :
    ∀ (xs : List Node), (∀ x ∈ xs, Incl (f x) (g x)) → Incl (meetList f xs) (meetList g xs)
  | [], _ => incl_refl _
  | x :: xs, h => incl_and_mono (h x (by simp)) (meetList_mono xs (fun y hy => h y (by simp [hy])))

/-- Below every summand ⇒ below the meet (shared worklist-step helper). -/
theorem incl_meetList {t : ESet n} {f : Node → ESet n} :
    ∀ (xs : List Node), (∀ x ∈ xs, Incl t (f x)) → Incl t (meetList f xs)
  | [], _ => incl_topV t
  | x :: xs, h => incl_and_intro (h x (by simp)) (incl_meetList xs (fun y hy => h y (by simp [hy])))

theorem incl_bot (t : ESet n) : Incl (0 : ESet n) t := by
  apply incl_iff.mpr
  intro i hi
  simp at hi

theorem gA_topSeed {P : Program} {nd : Node} (h : nd < P.size) :
    gA (topSeed P : Array (ESet n)) nd = topV n := by
  unfold topSeed; exact gA_ofFn (fun _ => topV n) h

theorem gA_botSeed {P : Program} {nd : Node} (h : nd < P.size) :
    gA (botSeed P : Array (ESet n)) nd = 0 := by
  unfold botSeed; exact gA_ofFn (fun _ => (0 : ESet n)) h

theorem incl_antisymm {a b : ESet n} (h1 : Incl a b) (h2 : Incl b a) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  exact Bool.eq_iff_iff.mpr ⟨incl_iff.mp h1 i, incl_iff.mp h2 i⟩

theorem arr_ext_gA {a b : Array (ESet n)} (hsz : a.size = b.size)
    (h : ∀ m, m < a.size → gA a m = gA b m) : a = b := by
  rw [Array.ext_iff]
  refine ⟨hsz, ?_⟩
  intro i h1 _
  have := h i h1
  rwa [gA_lt h1, gA_lt (hsz ▸ h1)] at this

/-- Pointwise monotonicity of a constraint `g` in its array argument. -/
def GMono (P : Program) (g : Array (ESet n) → Node → ESet n) : Prop :=
  ∀ (a b : Array (ESet n)), a.size = P.size → b.size = P.size →
    (∀ m, m < P.size → Incl (gA a m) (gA b m)) →
    ∀ m, m < P.size → Incl (g a m) (g b m)

/-- **Must per-index step**: a `mustStep`-fixpoint `X` below the running `arr` stays below the
    recomputed value. -/
theorem descInv_key {P : Program} {g : Array (ESet n) → Node → ESet n} (gmono : GMono P g)
    {X arr : Array (ESet n)} (hXsz : X.size = P.size) (harrsz : arr.size = P.size)
    (hXfix : ∀ m, m < P.size → gA X m = gA X m &&& g X m)
    (hInv : ∀ m, m < P.size → Incl (gA X m) (gA arr m)) {nd : Node} (hnd : nd < P.size) :
    Incl (gA X nd) (gA arr nd &&& g arr nd) :=
  incl_and_intro (hInv nd hnd)
    (incl_trans (incl_of_and_eq (hXfix nd hnd)) (gmono X arr hXsz harrsz hInv nd hnd))

/-- **May per-index step** (dual). -/
theorem ascInv_key {P : Program} {g : Array (ESet n) → Node → ESet n} (gmono : GMono P g)
    {X arr : Array (ESet n)} (hXsz : X.size = P.size) (harrsz : arr.size = P.size)
    (hXfix : ∀ m, m < P.size → gA X m = gA X m ||| g X m)
    (hInv : ∀ m, m < P.size → Incl (gA arr m) (gA X m)) {nd : Node} (hnd : nd < P.size) :
    Incl (gA arr nd ||| g arr nd) (gA X nd) :=
  incl_or_elim (hInv nd hnd)
    (incl_trans (gmono arr X harrsz hXsz hInv nd hnd) (incl_of_or_eq (hXfix nd hnd)))

/-- `solveMust` dominates every `mustStep`-fixpoint `X`. -/
theorem solveMust_dominates {P : Program} {g : Array (ESet n) → Node → ESet n} (gmono : GMono P g)
    {X : Array (ESet n)} (hXsz : X.size = P.size)
    (hXfix : ∀ m, m < P.size → gA X m = gA X m &&& g X m) :
    ∀ m, m < P.size → Incl (gA X m) (gA (solveMust P g) m) := by
  unfold solveMust
  have key := iterToFix_invariant (mustStep P g)
    (fun arr => arr.size = P.size ∧ ∀ m, m < P.size → Incl (gA X m) (gA arr m))
    (fun arr harr => ⟨mustStep_size P g arr, fun m hm => by
        rw [gA_step_must hm]; exact descInv_key gmono hXsz harr.1 hXfix harr.2 hm⟩)
    (measM P (topSeed P : Array (ESet n)) + 1) (topSeed P)
    ⟨topSeed_size P, fun m hm => by rw [gA_topSeed hm]; exact incl_topV _⟩
  exact key.2

/-- `solveMay` is dominated by every `mayStep`-fixpoint `X`. -/
theorem solveMay_dominated {P : Program} {g : Array (ESet n) → Node → ESet n} (gmono : GMono P g)
    {X : Array (ESet n)} (hXsz : X.size = P.size)
    (hXfix : ∀ m, m < P.size → gA X m = gA X m ||| g X m) :
    ∀ m, m < P.size → Incl (gA (solveMay P g) m) (gA X m) := by
  unfold solveMay
  have key := iterToFix_invariant (mayStep P g)
    (fun arr => arr.size = P.size ∧ ∀ m, m < P.size → Incl (gA arr m) (gA X m))
    (fun arr harr => ⟨mayStep_size P g arr, fun m hm => by
        rw [gA_step_may hm]; exact ascInv_key gmono hXsz harr.1 hXfix harr.2 hm⟩)
    (measV P (botSeed P : Array (ESet n)) + 1) (botSeed P)
    ⟨botSeed_size P, fun m hm => by rw [gA_botSeed hm]; exact incl_bot _⟩
  exact key.2

/-- `a ⊑ b ⇒ a = a &&& b` — the post-fixpoint reformulation feeding `solveMust_dominates`. -/
private theorem and_eq_of_incl {a b : ESet n} (h : Incl a b) : a = a &&& b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_and]
  by_cases hai : a.getLsbD i = true
  · rw [hai, incl_iff.mp h i hai, Bool.and_self]
  · simp only [Bool.not_eq_true] at hai; rw [hai, Bool.false_and]

/-- `b ⊑ a ⇒ a = a ||| b` — the pre-fixpoint reformulation feeding `solveMay_dominated`. -/
private theorem or_eq_of_incl {a b : ESet n} (h : Incl b a) : a = a ||| b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_or]
  by_cases hbi : b.getLsbD i = true
  · rw [incl_iff.mp h i hbi, hbi, Bool.or_self]
  · simp only [Bool.not_eq_true] at hbi; rw [hbi, Bool.or_false]

/-- **GENERIC must-extremality.** If the annotation `A` is a per-node post-fixpoint of a monotone
    transfer `g`, the worklist must-solver dominates it. The reusable core behind anti/avail/postp
    extremality. -/
theorem solveMust_extremal_of_postfix {P : Program} {g : Array (ESet n) → Node → ESet n}
    (gmono : GMono P g) {A : Node → ESet n}
    (hpost : ∀ m, m < P.size →
        Incl (A m) (g (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m)) :
    ∀ m, m < P.size → Incl (A m) (gA (solveMust P g) m) := by
  have hgAX : ∀ m, m < P.size →
      gA (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m = A m :=
    fun m hm => gA_ofFn (fun i : Fin P.size => A i.val) hm
  have hXfix : ∀ m, m < P.size →
      gA (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m
        = gA (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m
            &&& g (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m :=
    fun m hm => by rw [hgAX m hm]; exact and_eq_of_incl (hpost m hm)
  intro m hm
  have hdom := solveMust_dominates gmono Array.size_ofFn hXfix m hm
  rwa [hgAX m hm] at hdom

/-- **GENERIC may-extremality** (dual): if `A` is a per-node pre-fixpoint of a monotone transfer `g`,
    the worklist may-solver is dominated by it. The reusable core behind used/live extremality. -/
theorem solveMay_extremal_of_prefix {P : Program} {g : Array (ESet n) → Node → ESet n}
    (gmono : GMono P g) {A : Node → ESet n}
    (hpre : ∀ m, m < P.size →
        Incl (g (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m) (A m)) :
    ∀ m, m < P.size → Incl (gA (solveMay P g) m) (A m) := by
  have hgAX : ∀ m, m < P.size →
      gA (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m = A m :=
    fun m hm => gA_ofFn (fun i : Fin P.size => A i.val) hm
  have hXfix : ∀ m, m < P.size →
      gA (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m
        = gA (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m
            ||| g (Array.ofFn (n := P.size) (fun i : Fin P.size => A i.val)) m :=
    fun m hm => by rw [hgAX m hm]; exact or_eq_of_incl (hpre m hm)
  intro m hm
  have hdom := solveMay_dominated gmono Array.size_ofFn hXfix m hm
  rwa [hgAX m hm] at hdom

/-! ### The worklist engine dominates every fixpoint too -/

theorem wlStep_must_descInv {P : Program} {g : Array (ESet n) → Node → ESet n}
    {deps : Program → Node → List Node} (gmono : GMono P g) {X : Array (ESet n)}
    (hXsz : X.size = P.size) (hXfix : ∀ m, m < P.size → gA X m = gA X m &&& g X m)
    {s : WL n} (hwl : WLInv P s) (hInv : ∀ m, m < P.size → Incl (gA X m) (gA s.arr m)) :
    ∀ m, m < P.size → Incl (gA X m) (gA (wlStep g (· &&& ·) (readersOf P deps) s).arr m) := by
  obtain ⟨arr, q⟩ := s
  obtain ⟨hsz, hrange⟩ := hwl
  cases q with
  | nil => intro m hm; simp only [wlStep]; exact hInv m hm
  | cons nd q' =>
      have hndlt : nd < P.size := hrange nd (by simp)
      have hndarr : nd < arr.size := by rw [hsz]; exact hndlt
      by_cases hch : (gA arr nd &&& g arr nd) = gA arr nd
      · rw [wlStep_cons_noop hch]; exact hInv
      · rw [wlStep_cons_change hch]
        intro m hm
        by_cases hmnd : m = nd
        · subst hmnd
          rw [gA_set_eq hndarr]
          exact descInv_key gmono hXsz hsz hXfix hInv hndlt
        · rw [gA_set_ne hmnd]
          exact hInv m hm

theorem wlStep_may_ascInv {P : Program} {g : Array (ESet n) → Node → ESet n}
    {deps : Program → Node → List Node} (gmono : GMono P g) {X : Array (ESet n)}
    (hXsz : X.size = P.size) (hXfix : ∀ m, m < P.size → gA X m = gA X m ||| g X m)
    {s : WL n} (hwl : WLInv P s) (hInv : ∀ m, m < P.size → Incl (gA s.arr m) (gA X m)) :
    ∀ m, m < P.size → Incl (gA (wlStep g (· ||| ·) (readersOf P deps) s).arr m) (gA X m) := by
  obtain ⟨arr, q⟩ := s
  obtain ⟨hsz, hrange⟩ := hwl
  cases q with
  | nil => intro m hm; simp only [wlStep]; exact hInv m hm
  | cons nd q' =>
      have hndlt : nd < P.size := hrange nd (by simp)
      have hndarr : nd < arr.size := by rw [hsz]; exact hndlt
      by_cases hch : (gA arr nd ||| g arr nd) = gA arr nd
      · rw [wlStep_cons_noop hch]; exact hInv
      · rw [wlStep_cons_change hch]
        intro m hm
        by_cases hmnd : m = nd
        · subst hmnd
          rw [gA_set_eq hndarr]
          exact ascInv_key gmono hXsz hsz hXfix hInv hndlt
        · rw [gA_set_ne hmnd]
          exact hInv m hm

/-- `solveWLMust` dominates every `mustStep`-fixpoint `X`. -/
theorem solveWLMust_dominates {P : Program} {g : Array (ESet n) → Node → ESet n}
    {deps : Program → Node → List Node} (gmono : GMono P g)
    (hdeps : ∀ (nd : Node), ∀ m ∈ (readersOf P deps)[nd]?.getD ([] : List Node), m < P.size)
    {X : Array (ESet n)} (hXsz : X.size = P.size)
    (hXfix : ∀ m, m < P.size → gA X m = gA X m &&& g X m) :
    ∀ m, m < P.size → Incl (gA X m) (gA (solveWLMust P g deps) m) := by
  have hinv := wlRun_invariant (wlStep g (· &&& ·) (readersOf P deps))
    (fun s => WLInv P s ∧ (∀ m, m < P.size → Incl (gA X m) (gA s.arr m)))
    (fun s hs => ⟨wlStep_WLInv hdeps hs.1, wlStep_must_descInv gmono hXsz hXfix hs.1 hs.2⟩)
    (wlMeas (n := n) P measM deps (wlInit P (topSeed P)) + 1) (wlInit P (topSeed P))
    ⟨⟨topSeed_size P, fun k hk => List.mem_range.mp hk⟩,
     fun m hm => by
        rw [show gA (wlInit P (topSeed P)).arr m = gA (topSeed P) m from rfl, gA_topSeed hm]
        exact incl_topV _⟩
  exact hinv.2

/-- `solveWLMay` is dominated by every `mayStep`-fixpoint `X`. -/
theorem solveWLMay_dominated {P : Program} {g : Array (ESet n) → Node → ESet n}
    {deps : Program → Node → List Node} (gmono : GMono P g)
    (hdeps : ∀ (nd : Node), ∀ m ∈ (readersOf P deps)[nd]?.getD ([] : List Node), m < P.size)
    {X : Array (ESet n)} (hXsz : X.size = P.size)
    (hXfix : ∀ m, m < P.size → gA X m = gA X m ||| g X m) :
    ∀ m, m < P.size → Incl (gA (solveWLMay P g deps) m) (gA X m) := by
  have hinv := wlRun_invariant (wlStep g (· ||| ·) (readersOf P deps))
    (fun s => WLInv P s ∧ (∀ m, m < P.size → Incl (gA s.arr m) (gA X m)))
    (fun s hs => ⟨wlStep_WLInv hdeps hs.1, wlStep_may_ascInv gmono hXsz hXfix hs.1 hs.2⟩)
    (wlMeas (n := n) P measV deps (wlInit P (botSeed P)) + 1) (wlInit P (botSeed P))
    ⟨⟨botSeed_size P, fun k hk => List.mem_range.mp hk⟩,
     fun m hm => by
        rw [show gA (wlInit P (botSeed P)).arr m = gA (botSeed P) m from rfl, gA_botSeed hm]
        exact incl_bot _⟩
  exact hinv.2

/-! ### The refinement equalities (mutual domination + `Incl`-antisymmetry) -/

/-- **The worklist must-solve equals the naive Kleene must-solve**, for any monotone `g` whose readers
    are `deps`. -/
theorem solveWL_eq_must {P : Program} {g : Array (ESet n) → Node → ESet n}
    {deps : Program → Node → List Node} (gmono : GMono P g)
    (hdeps : ∀ (nd : Node), ∀ m ∈ (readersOf P deps)[nd]?.getD ([] : List Node), m < P.size)
    (hloc : ∀ (arr : Array (ESet n)) (nd : Node) (v : ESet n) (m : Node),
        m ∉ deps P nd → g (arr.set! nd v) m = g arr m) :
    solveWLMust P g deps = solveMust P g := by
  have hWLsz : (solveWLMust P g deps).size = P.size := solveWL_size (topSeed_size P) hdeps
  have hMsz : (solveMust P g).size = P.size := solveMust_size P g
  have hWLfix : ∀ m, m < P.size → gA (solveWLMust P g deps) m
        = gA (solveWLMust P g deps) m &&& g (solveWLMust P g deps) m :=
    solveWL_settled (topSeed_size P) hdeps
      (fun arr nd h1 h2 h3 => must_hdrop arr nd h1 h2 h3) hloc and_idem_right
  have hMfix : ∀ m, m < P.size → gA (solveMust P g) m
        = gA (solveMust P g) m &&& g (solveMust P g) m := fun m hm => solveMust_eq P g hm
  have h1 := solveMust_dominates gmono hWLsz hWLfix          -- WL ⊆ Must
  have h2 := solveWLMust_dominates gmono hdeps hMsz hMfix    -- Must ⊆ WL
  apply arr_ext_gA (by rw [hWLsz, hMsz])
  intro m hmlt
  rw [hWLsz] at hmlt
  exact incl_antisymm (h1 m hmlt) (h2 m hmlt)

/-- **The worklist may-solve equals the naive Kleene may-solve** (dual). -/
theorem solveWL_eq_may {P : Program} {g : Array (ESet n) → Node → ESet n}
    {deps : Program → Node → List Node} (gmono : GMono P g)
    (hdeps : ∀ (nd : Node), ∀ m ∈ (readersOf P deps)[nd]?.getD ([] : List Node), m < P.size)
    (hloc : ∀ (arr : Array (ESet n)) (nd : Node) (v : ESet n) (m : Node),
        m ∉ deps P nd → g (arr.set! nd v) m = g arr m) :
    solveWLMay P g deps = solveMay P g := by
  have hWLsz : (solveWLMay P g deps).size = P.size := solveWL_size (botSeed_size P) hdeps
  have hMsz : (solveMay P g).size = P.size := solveMay_size P g
  have hWLfix : ∀ m, m < P.size → gA (solveWLMay P g deps) m
        = gA (solveWLMay P g deps) m ||| g (solveWLMay P g deps) m :=
    solveWL_settled (botSeed_size P) hdeps
      (fun arr nd h1 h2 h3 => may_hdrop arr nd h1 h2 h3) hloc or_idem_right
  have hMfix : ∀ m, m < P.size → gA (solveMay P g) m
        = gA (solveMay P g) m ||| g (solveMay P g) m := fun m hm => solveMay_eq P g hm
  have h1 := solveMay_dominated gmono hWLsz hWLfix            -- May ⊆ WL
  have h2 := solveWLMay_dominated gmono hdeps hMsz hMfix      -- WL ⊆ May
  apply arr_ext_gA (by rw [hWLsz, hMsz])
  intro m hmlt
  rw [hWLsz] at hmlt
  exact incl_antisymm (h2 m hmlt) (h1 m hmlt)

end Solver
