# SISSA AI Safety School Lean Workshop
This repo contains the material for the Lean tutorial at the SISSA AI Safety School.
This consists of various Lean files with proofs and occasionally definitions to fill in _by hand_.
The goal here is for participants to gain some familiarity with how one goes about writing Lean proofs and formalising mathematics.

## Prerequisites
For this tutorial, you'll need 
- VS Code: install [here](https://code.visualstudio.com/),
- Lean: install [here](https://lean-lang.org/getting-started/#install-lean-locally),
- Git: if it's not natively installed on your machine, follow the instructions [here](https://git-scm.com/install/windows) (Linux and MacOS machines usually have it by default). You can check whether it's installed on your machine by opening a terminal and typing `git version`. This should output something like `git version ...` if Git is installed.

## Getting started
Once you've installed VS Code and Lean, here's what you can get started by doing the following. 
In a terminal, run the following commands:
```bash
# Clone the repository
git clone https://github.com/Paul-Lez/LeanSISSA
# Open the cloned repository in VS Code
code LeanSISSA
```
Once you're in VS Code, open a terminal and run
```bash
# Collect the build cache for Mathlib (if you're not familiar with Lean, this is to avoid recompiling the math whole library yourself)
lake exe cache get
# Build (i.e. compile) the Lean code in LeanSISSA 
lake build
```

## Link to Lean Live editor for the session
If you're struggling to get things working on your machine, you can use the online Lean Live Editor to follow (and code along) during the first live session.
[Here's a link to the editor with the file for the first session loaded](https://live.lean-lang.org/#codez=LYewJgrgNgpgUHADhARlAlgYwATuIkAJwBdsBZAQ2IAsMUEB6AWgEJsBibAQWwGdgKUKNjAxQ2AGbpYCACrV0vSdJjZMIAHbEK6DUoqSYAd2woKvLCLEglxEH2ogTjkwBkYFDdiNEA1rzgmBgRkNEteGExidE0EOPiExKTkxiZseVUzCxxeAE8tCgAPbE8wbG0orF4AOmwg1LTZQnRPAHNoCkJsDQhgFBhCfUJVHr6BpRAJcupVCSJgbEBEIgB9AG90bEATImwABgBfAD0vdFr60Smmlo12qE6AOV7%2BroAKLwAubEBUQgBKbA%2FPv4AXiWuGwgAgibAAMV0EWI1QAkpgcABGboAGlwCBoMCIYnKzTaHUIDzGhGWvAgSL%2B2EAAETo9IE65EklPbCvbAAamwyN%2BwMuhNuxMeA26nLZXi5PKBplycGwfCIhFlcGxuIWxEZN3uwrJAC8BvYPvymYKWSKdthgRa3sCULL5bxFcrVcMFjBCopiLxlhqrlqhaTljAAI7UwDARPTjf6zV0vMCAGzSu1yhWEJUId0UfCwcP0i0AHgZfuZOtFgHIibAAZmwgGIiIsC7Wk0U2mUpx1p5UpFIuvG6KQadDECCiZaTZaIZrAGBKD50u4YiOIbCAUyJsPO11RqgAFSeqJct5PyphpCcgABuqggFmu2AABndN%2B7Pd6J3gYMtSsswGewLe206uxSY9uGwU9ICibBJhKPhekgqZeGDCBOmnXB9BghYoIQpDhhqFUZjVUxCAoagBHaRBtGWKQUE0CgkQ2Z4DBQNQRGpQASQl%2BN4U3lBjsAObAACYxSYvj%2BN%2BAAqNkcBEsUyhE3k2QMCScDSJiJLAX5pK5Hi1KE7AlI0gSk3tVN00Asy4mYOAuCgVoYBQIjwg1SkhxwwJgkCNJ3FIW8AHFb1MVQDFaQgQAgRA4DPToWjQVRVh86lZFyRAYD2bAAG0fJCsLsB8gBdCKoooGKFNMZiPh874EGAgB1VRME8bAr1UbFGopQRsGAaBokQDB6uiC9uhAbRoliTNs1UD5FLZVS1Hk7TTHEsrAX%2FDsqs8mBvIAJX8%2FpoPUYBOuG9ABuaa4CoJYrVk2hKkpS9KAGEQAOzbdFabBNvy8zUiswwTHUDQJCvV7plepQGBglBiBzGhQbchBIounNnmKf5KrgZhsEegZMBiPQ6nc4D2EwGZMF8bBCg8jhiciMmmGRSmiZJsnnjptjfi5CnKbGnrVB4pjUbZAAJakDG2FAOJKj52K2UqD1lYCHQA9G0gAKQgDQyciqAIBQ%2BpCep0nuWwcGdgZmAtaNk2GYNsnUXB%2FizYtu2BOtpnsEALCIWewAAOSqgA)

## Course website

The [course website](https://paul-lez.github.io/LeanSISSA/) has resource links and tactic and command cheatsheets.
