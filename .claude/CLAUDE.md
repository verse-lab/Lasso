# Notes

This project uses the Lentil library as the semantics foundation. 

## General Tips

- When declaring type parameters, make them universe polymorphic if possible. 
- Search on Loogle first for required things from libraries. Otherwise, first check `lean-toolchain` before looking at local Lean source code. Searching under `.lake/packages/` is also useful sometimes. 
- Create a local temp file if you want to do some experiments, instead of writing into some file in `/tmp/`. If you want to edit it, just edit it, don't do it at the CLI level. 

## Notes on general file structure

- Most of our work will require abstract specifications and proofs of refinement (or executable code implements said refinement), such abstract specifications should be kept in a seperate sub-folder called "AbstractSpec". Files inside "AbstractSpec" should not import from the non-abstract files outside it. They can import from other abstract specifications or from the LTL folder (or even Lentil if necessary for some reason)
- Definitions on structures should be defined in the same file as the structure itself is whenever possible. For example when there is a "structure Node" definition, then Node.toSpec should be defined in that same file instead of defining Node.toSpec somewhere else. Keep definitions local.
- Definitions used in any file should not be imported transitively, the actual file that defines it should be added to the list of imports (only for project files, not for e.g. Mathlib or Lentil imports)
- Files should be structured with /-! ## SECTION -/ comments

## Notes When Writing Proofs

- Use `grind` aggressively !! It is very powerful and can discharge most mechanical proofs. It is far better than fighting Lean's intricasies.
- Keep minimal assumptions. For example, if there is an inductive type `A t` parameterized over `t : Type u`, and it's possible to derive `LawfulBEq (A t)` by assuming `LawfulBEq t`, then you should just assume `LawfulBEq t` instead of `LawfulBEq (A t)`. 
- Reducing a match h : e with term against a known equation needs rw, not simp only (motive-dependence blocks the latter every time); reducing a struct-literal's own field projection needs neither — exact/refine see through it by plain defeq, so the working style throughout was deriving each field as a have phrased over the un-reduced expression and closing with one final exact ⟨...⟩.
- Before defining auxiliary `theorem`s, first check if related ones can be found in the existing library. 
- If possible, please pause whenever you think you might need to write huge proofs about something and explain to me the situation, then we can chat. 
- Please organize the theorems properly to avoid `omit ... in` warnings. 

## Proofs
- Try to not take any shortcuts that can bite us again later, even if doing it properly is more involved. I prefer a longer session to do it cleanly once than having to do something later again. Keep theorems generalized, try not to proof something "for this case only" especially if you already know I will likely add another case later, always prove it for the general case directly instead.
- For many harder things we proof, somebody has likely already proven it before on pen-and-paper. Feel free to look up those academic papers that include these proofs without consulting me (just tell me). It is better to cite them and implement their proof strategy than to try to reinvent the proof. SCC sufficiency is a great example of something that has almost certainly been proven already.

## Comments style
- Each file should have one top-level comment block detailing what the file defines, what it proves (core theorems, other important ones) and academic references if any (e.g. proof structure from this paper), for code include the pseudo-code I give you. Include a "sections" section with a list of all subsection (i.e. comments where you used /-- ## SUBSECTION_NAME -/)
- Include a shortened reference to an academic paper in the comment of a theorem where fitting. For example if we're reusing the overall proof structure from a hand-written proof, reference that shortly on the comment of that theorem.
- Avoid large comment blocks on theorems or code, instead keep them short and sweet. I prefer single-line comments or two lines (unless you add other things I told you to add, like the academic references or the list of invariants necessary for this to hold etc.). If you want to highlight something, add another single-line comment inside the code instead of making the comment-block bigger. You can make comment blocks on theorems for example for listing the invariants that need to be preserved to proof it, or other such very general information, but nothing about proof-tricks it uses or any of the sort.
- Core theorems should have at least a single line comment that spells the theorem out.
- Private theorems usually require no explanation at all.
- Single line comments on fields of a def, struct, etc. should be "--" instead of "/-", even when it is on their own line above the actual field definition.
- Use no * highlighting in comments.
- Do not use sentences with ";" or the "—" but replace them with commas, punctuation, ", and", ", therefore" and so on (unless in places where they are standard, for example in academic references the "—" and ";" is very common and standard use, but I don't use them usually in my normal comments and texts).
- There can be no new line inside a ` ... ` highlighted part in the comment, as this causes rendering issues in the IDE.
- Prefer longer lines in comments (e.g. >140 characters) instead of going to a new line in the same sentence, there is no reason to move to a new line for just a couple of words, keep them on the same line. Punctuation ("." or ",") are great places to move to a new line instead.
- Do not write down historical records in your comments (used to be this, now this, that is why). No need to write down how it used to be earlier. Only how it is now, and maybe why it makes sense. When this is published later, any user need not to know the entire development process, it is more important that they can quickly go through everything and make some sense of it, and such huge comment blocks makes this harder.
- There is no need to add explainers to theorems about how they should be used or what other theorems they enable etc., any user can just look that up. It simply proves something, and how we use that something in other theorems can be explained in those other theorems if necessary, but again keep comments small and explain only what is really required.
- Feel free to shorten already existing comments if you think they do not match these standards. For /Examples files I will provide you a different set of standards !! Examples require a different style of comments, this is not sufficient there.
- Descriptions of individual fields in definitions (or structures, or inductive defintions etc.) should be inline, using a "--" comment on or above that line and not a block comment on the entire thing. Here is an example of how it should not look, instead these rules should be inline comments (using "--") on each of the cases inside the def, instead of a top-level comment-block:
```
/-- Second set of new formulas for non-deterministic expansion.
  new2 (μ U ψ) = {ψ}       -- take the "satisfy now" branch
  new2 (μ R ψ) = {μ, ψ}    -- take the "release now" branch
  new2 (μ ∨ ψ) = {ψ}       -- take the second disjunct
  new2 _       = {} -/
def new2 {α} : NNF α → List (NNF α)
  | .until _ ψ => [ψ]
  | .release μ ψ => [μ, ψ]
  | .or _ ψ => [ψ]
  | _ => []
```
- No lean proof details or any of the similar like "it combines these other theorems ...", an example of something that should not be commented it the following text: "Defined using `partial_fixpoint` (`Option` return type), which gives equational rewrite lemmas (`rw [expand]`) and a `partial_correctness` induction principle without requiring a termination proof." or "Requires `[BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]`." or "Combines `constructGBA_iff_expandOASpec` (`Bridge.lean`) with `expandOASpec_soundness` (`Soundness.lean`) and `expandOASpec_completeness` + `createGraph_graphComplete` (`Completeness.lean`)". These are things anybody with the tiniest Lean knowledge can instantly see.
- Do not add details that are painfully obvious to anyone with a bit of code knowledge, and remove any such comments when you come across them. This repository will be looked at mainly by people who know Lean well, a lot of them even experts. Things like 1-line comments on cases inside proofs can be kept for readability and making it easier for even experts to faster understand what is going on in the code. This is an example of a comment that is completely unnecessary since it is very obvious:
```
/-- Create the full node graph from an LTL formula.

The initial node has:
- `name = 1` (the first fresh name after `expandInit = 0`)
- `incoming = {expandInit}` (marks it as reachable from init)
- `new = {φ}` (the formula to check)
- `old = {}, next = {}` (empty)
-/
def createGraph (φ : NNF α) : Option (ExpandState α S) :=
  let initNode : ExpansionNode α S := {
    name := 1  -- first fresh name after expandInit = 0
    incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit
    new := [φ]
    old := FSet.empty
    next := FSet.empty
  }
  ...
```
- Do not go to the next line too early on a comment block, I have no problem with there being >130 characters on a single line in a comment. For example if there is only one or two more words before a comma, keep them in the same line, then comma, then next line. Keep the line count small and increase the length of the lines rather instead.

I want you to apply these comments style standards rather aggressively and always in any code you write. Keep the comments short.

## Persistent memory
- If you want to keep more notes for yourself than what you commented as per "Comments style" section, write them down in a .md file in a /tmp/ folder inside this repository, as I want to keep the comments rather small. You should write down any information you might need again in a future session without consulting me. I will not be able to finish most things in a single session, so it is important you can pick it up again later without having to rediscover everything again.