# Notes

This project uses the Lentil library as the semantics foundation. 

## General Tips

- When declaring type parameters, make them universe polymorphic if possible. 
- Search on Loogle first for required things from libraries. Otherwise, first check `lean-toolchain` before looking at local Lean source code. Searching under `.lake/packages/` is also useful sometimes. 
- Create a local temp file if you want to do some experiments, instead of writing into some file in `/tmp/`. If you want to edit it, just edit it, don't do it at the CLI level. 

## Notes When Writing Proofs

- Use `grind` cleverly. It's very powerful, so if you start thinking about using `tauto` or `aesop`, please try `grind` first. 
- Keep minimal assumptions. For example, if there is an inductive type `A t` parameterized over `t : Type u`, and it's possible to derive `LawfulBEq (A t)` by assuming `LawfulBEq t`, then you should just assume `LawfulBEq t` instead of `LawfulBEq t`. 
- Before defining auxiliary `theorem`s, first check if related ones can be found in the existing library. 
- If possible, please pause whenever you think you might need to write huge proofs about something and explain to me the situation, then we can chat. 
- Please organize the theorems properly to avoid `omit ... in` warnings. 
