From the latest Documentation

# Setup
It is done already.
If not already done via:
Setup your LEAN Environment

Setup your environment to get the most out of Aristotle.
Install Lean

You need Lean4 installed on your computer. You can install it at https://lean-lang.org/install/.
Pin Lean Version

Aristotle is compatible with Lean v4.28.0. To use this version, ensure your lean-toolchain file contains exactly the below.

leanprover/lean4:v4.28.0

Pin Mathlib Version

Aristotle is compatible with Mathlib v4.28.0. Make sure your lakefile.toml contains the below.

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.28.0"

Verify your Project builds

Ensure your project builds successfully.

lake exe cache get; lake build


# Install CLI
If not already done. It is done already.
Install the CLI

Use Aristotle in your terminal with a simple command.
Install UV

We recommend using UV for package management. You can install UV here. Aristotle is also distributed via pip.
Install Aristotle

Install the Aristotle CLI globally — no virtual environment or project setup required:

uv tool install aristotlelib

Then call

aristotle --help

to see available options.
Or install with pip

If you prefer a traditional install into an existing virtual environment:

pip install aristotlelib

Keeping aristotlelib updated

Make sure to update aristotlelib regularly to access new features and improvements:

uv tool upgrade aristotlelib

Or add the below to your ~/.bashrc, ~/.zshrc, or similar file to always use the latest version automatically:

alias aristotle='uvx --from aristotlelib@latest aristotle'


# Ask Question
This is key:
Submit your first question!

See the docs for more examples and the complete CLI reference

uv run aristotle submit "Prove that there are infinitely many primes." --project-dir .



# Docs

More info:

## Overview
Overview

Aristotle is a verified reasoning agent by Harmonic that proves and formally verifies graduate and research-level problems in mathematics, software, and more using Lean 4.
What Aristotle Can Do

Fill sorries

Fill sorries in your Lean project — submit a file and Aristotle fills in all sorry placeholders with verified proofs.

Formalize mathematics

Formalize mathematics — give Aristotle a paper, textbook, or notes in natural language and it produces formal Lean proofs.

Prove from prompts

Prove from prompts — describe a theorem in plain English and Aristotle formalizes and proves it.

Find counterexamples

Find counterexamples — when a statement is false, Aristotle can disprove it and surface a counterexample.
Two Ways to Use Aristotle

CLI — run aristotle from your terminal to submit projects, download results, and manage your work.

aristotle submit "Prove that the square root of 2 is irrational" --wait

Python API — use the aristotlelib package programmatically for automation and integration.
python

import asyncio
from aristotlelib import Project

async def main():
    project = await Project.create(
        prompt="Prove that the square root of 2 is irrational"
    )
    tasks, _ = await project.get_tasks(limit=1)
    await tasks[0].wait_for_completion()
    await project.get_files(destination="output.tar.gz")

asyncio.run(main())

To get started, see Installation.


## Submitting Jobs
Submitting Projects
Fill Sorries in a Lean Project

Submit a Lean project to Aristotle and it will fill in all the sorry placeholders with verified proofs.

aristotle submit "Fill in the sorries" --project-dir ./my-lean-project --wait

Or via the Python API:
python

from aristotlelib import Project

project = await Project.create_from_directory(
    prompt="Fill in the sorries",
    project_dir="./my-lean-project",
)
tasks, _ = await project.get_tasks(limit=1)
await tasks[0].wait_for_completion()
await project.get_files(destination="output.tar.gz")

Project Requirements

Your Lean project should include:

    A lakefile.toml (or lakefile.lean) configuration file
    A lean-toolchain file specifying the Lean version
    .lean source files with proper import structure

A typical layout:

my-lean-project/
├── lakefile.toml
├── lean-toolchain
├── lake-manifest.json
└── MyLeanProject/
    ├── Basic.lean
    └── Main.lean

The SDK automatically packages your directory for upload, skipping build artifacts (.olean, .lake/packages/).
Guide Aristotle with Natural Language Proof Sketches

You can provide natural language hints to guide Aristotle's proof search. Include your proof sketch in the header comment of the theorem, tagged with PROVIDED SOLUTION. Your sketch can be as general or as detailed as you like.
lean

/--
Given x, y ∈ [0, π/2], show that cos(sqrt(x ^ 2 + y ^ 2)) ≤ cos x * cos y.

PROVIDED SOLUTION
Set r := sqrt(x^2 + y^2). If r > π/2, then the inequality holds trivially.
So consider the case r ≤ π/2. Write x = r cos φ, y = r sin φ.
Consider the function F(φ) := log(cos(r cos φ)) + log(cos(r sin φ)). Then
F(0) = F(π/2) = log r, so it suffices to show that for F(φ) ≥ F(0) = F(π/2).
The derivative of F is F'(φ) = r(sin φ tan(r cos φ) - cos φ tan(r * sin φ)).
Define G(u) := tan u / u. The derivative of G on (0, π/2) is
(u - sin u cos u) / (u ^ 2 * (cos u) ^ 2), which is nonnegative on (0, π/2),
so G is increasing on (0, π/2).

For φ in [0, π/4], we have r * cos φ ≥ r * sin φ, so by monotonicity of G,
tan(r * cos φ)/(r * cos φ) ≥ tan(r * sin φ)/(r * sin φ). On [π/4, π/2],
the inequality is reversed. Multiplying this by r^2 cos φ sin φ gives that
F' is nonnegative on [0, π/4] and nonpositive on [π/4, π/2]. This means that
for φ in [0, π/4], F(φ) ≥ F(0), and for φ in [π/4, π/2], F(φ) ≥ F(π/2),
completing the proof.
-/
theorem final (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ Real.pi / 2) (hy : 0 ≤ y) (hy' : y ≤ Real.pi / 2) :
    Real.cos (Real.sqrt (x ^ 2 + y ^2)) ≤ Real.cos x * Real.cos y := by
  sorry

Aristotle does not see comments inside proof blocks.
Counterexamples and Negations

Aristotle can disprove false statements and find counterexamples, helping you identify logical errors, missed edge cases, or misformalizations. When a statement is false, Aristotle leaves a comment on the theorem with a proof of the negation.
lean

/-
Aristotle found this block to be false.
Here is a proof of the negation:
theorem my_favorite_theorem (k : ℕ) :
  ∑' n : ℕ, (1 : ℝ) / Nat.choose (n + k + 1) n = 1 + 1 / k := by
    -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state;
    -- Proof starts here:
    use 0; norm_num;
    erw [ tsum_eq_zero_of_not_summable ] <;> norm_num;
    exact_mod_cast mt ( summable_nat_add_iff 1 |> Iff.mp ) Real.not_summable_natCast_inv
-/
theorem my_favorite_theorem (k : ℕ) :
    ∑' n : ℕ, (1 : ℝ) / Nat.choose (n + k + 1) n = 1 + 1 / k := by
  sorry

The custom negate_state tactic is automatically included in the file header. Source:
lean

import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try push_neg
  )
)

Working with Data

Aristotle does not modify your definitions by default. For example, the following will not be changed:
lean

def foo : Nat := by sorry

Aristotle will create its own data where needed.
Submit a Prompt

You can use Aristotle in plain English — no Lean required. Ask anything, from specific math problems to general conceptual questions:

aristotle submit "Prove that the square root of 2 is irrational" --wait

aristotle submit "Implement Newton iteration and prove it correct" --wait

Or via the Python API:
python

from aristotlelib import Project

project = await Project.create(
    prompt="Prove that the square root of 2 is irrational",
)
tasks, _ = await project.get_tasks(limit=1)
await tasks[0].wait_for_completion()
await project.get_files(destination="output.tar.gz")

Formalize a Document

Submit a document containing mathematics in natural language — such as a .tex, .txt, or .md file — and Aristotle will produce formal Lean proofs:

aristotle formalize paper.tex --wait --destination output.tar.gz

Providing Context

When submitting with --project-dir, you can include supplementary files that help Aristotle understand your problem:

aristotle submit "Formalize the main theorems" --project-dir ./my-paper --wait

The directory can contain:

    Lean files — definitions, theorems, and structures you want Aristotle to be aware of. Aristotle will automatically resolve transitive dependencies but will not modify context files.
    Text files — textbook chapters, personal notes, or hints to guide Aristotle.

Context is optional — Aristotle can make progress without it.
Prompt Cookbook

Aristotle is smart and flexible — you can easily guide it with natural language prompts. Here are effective prompts for common use cases.
Sorry Filling

Fill in all the sorries in this project

Flexibility

Prove this using only `ring` and `omega`, avoiding heavy automation

Accessibility

Fill in the sorries and add detailed docstrings explaining each definition, theorem, and proof step for Lean beginners

Modularity

Refactor this file into a modular structure: extract helper lemmas, group related definitions, and minimize imports

Proof Optimization

Golf all the proofs in this project: minimize tactic count and simplify where possible

Proof Repair

Fix all compilation errors and linter warnings in this project

Auxiliary Lemmas

Build auxiliary lemmas that would help prove the main sorry'd goal in this file

API Development

Develop API lemmas for the main structure in this file: coercions, simp lemmas, and basic properties

Formal Skeleton

Build a formal sorry'd skeleton closely following my paper, with theorem statements matching each result

Code Quality

Formalize this paper and make sure the code quality closely follows Mathlib standards

## Managing projects
Managing Projects
Listing Projects

aristotle list

Lists the 10 most recent projects, newest first. Use --limit (1–100) and --pagination-key to page through older results, and --status to filter.

aristotle list --status RUNNING --limit 50

Only RUNNING and IDLE are accepted — see Project vs Task Status.
Inspecting a Project

aristotle show <project-id>

Prints the latest task on the project along with its most recent events. If the task is still running, show live-tails events until it completes.

--task <task-id> inspects a specific historical task. --limit N limits how many events are shown.
Listing Tasks

aristotle tasks <project-id>

The initial submit creates a task. ask steers the current task if it is still running, or starts a follow-up task if the project is idle. tasks lists project tasks, newest first, with the same --limit and --pagination-key flags as list.
Follow-up Prompts

aristotle ask <project-id> "Golf the proofs and remove unused imports"

Steers the current task if it is still running, or starts a follow-up task if the project is idle. Use it to iterate on a result, or to resume after COMPLETE_WITH_ERRORS or OUT_OF_BUDGET.
Downloading Results

aristotle download <project-id> --destination output.tar.gz

Downloads the current state of the project.
Canceling

aristotle cancel <project-or-task-id>

Cancels the most recent task on the project. The command accepts either a project ID or a task ID:

aristotle cancel --task-id <task-id>
aristotle cancel --project-id <project-id>

Use the explicit flags when you want to make the ID type unambiguous.
Project vs Task Status

Project status tells you whether Aristotle is currently working on the project. Task status tells you where a specific task is in its lifecycle.
Project Status

    RUNNING — at least one task is queued or in progress.
    IDLE — no task is currently running.

aristotle list --status accepts only these two values.
Task Status

Returned by aristotle show, aristotle tasks, and the SDK's AgentTask.status.

    QUEUED — waiting to be processed.
    IN_PROGRESS — Aristotle is working on the task.
    COMPLETE — finished successfully.
    COMPLETE_WITH_ERRORS — partial progress; usually worth a clarifying aristotle ask.
    OUT_OF_BUDGET — compute exhausted; partial results typically available. Resume with aristotle ask.
    FAILED — internal error. The Harmonic team is notified automatically.
    CANCELED — canceled.

## SDK Reference
SDK Reference

aristotlelib is the official Python client for the Aristotle API. Every method that issues a network request is async.
python

import aristotlelib
from aristotlelib import (
    Project,
    ProjectStatus,
    AgentTask,
    TaskStatus,
    Event,
    EventType,
    AristotleAPIError,
)

Authentication

Set your API key before creating projects:
python

# Option 1: environment variable (recommended)
# export ARISTOTLE_API_KEY='arstl_...'

# Option 2: set programmatically
aristotlelib.set_api_key("arstl_...")

Concepts

A Project groups one or more AgentTasks. Creating a project schedules its first task; project.ask(...) steers the current task if it is still running, or starts a follow-up task if the project is idle. ProjectStatus is coarse (RUNNING or IDLE); TaskStatus carries the granular outcome of each task.
Project
Project.create(prompt, tar_file_path=None, public_file_path=None)

Submits a new project. tar_file_path is an optional .tar.gz of supplementary files; public_file_path sets the filename recorded by Aristotle.
python

project = await Project.create(prompt="Prove that 1 + 1 = 2")

Project.create_from_directory(prompt, project_dir)

Submits a new project from a local directory.
python

project = await Project.create_from_directory(
    prompt="Fill in the sorries",
    project_dir="./my-project",
)

Project.from_id(project_id)

Loads a project by ID.
Project.list_projects(pagination_key=None, limit=30, status=None)

Returns (projects, next_pagination_key), newest first. limit ranges from 1 to 100. status accepts a single ProjectStatus or a list, and filters returned projects to those statuses.
python

projects, next_key = await Project.list_projects(limit=10)
running, _ = await Project.list_projects(status=ProjectStatus.RUNNING)

project.ask(prompt)

Steers the current task if it is still running, or starts a follow-up task if the project is idle. Returns the updated or new task.
python

task = await project.ask("Golf the proofs and remove unused imports.")
await task.wait_for_completion()

project.get_tasks(pagination_key=None, limit=10, newest_first=True)

Returns (tasks, next_pagination_key).
project.get_files(destination=None)

Refreshes the project, then downloads the result tarball if available or the original input otherwise. If destination is omitted, the file is downloaded in the current directory.
python

path = await project.get_files(destination="output.tar.gz")

project.refresh()

Refreshes the project's state in place.
Fields

project_id, description, status (ProjectStatus), created_at, last_updated, has_input, has_files.
Waiting for a project to finish

Project does not expose wait_for_completion. Wait on its latest task instead:
python

project = await Project.create_from_directory(
    prompt="Fill in the sorries",
    project_dir="./my-project",
)
tasks, _ = await project.get_tasks(limit=1)
await tasks[0].wait_for_completion()
await project.get_files(destination="output.tar.gz")

AgentTask
AgentTask.from_id(agent_task_id)

Loads a task by ID.
task.wait_for_completion(num_events=3, poll_interval_seconds=5)

Polls until the task reaches a terminal state, streaming num_events recent events to stdout. Pass num_events=0 to poll silently. Inspect task.status after it returns.
task.get_events(pagination_key=None, limit=50, newest_first=True)

Returns (events, next_pagination_key). Each event represents one step Aristotle took during the task.
task.show(num_events=0, pagination_key=None)

Prints a snapshot of the task and its most recent events. Returns the next pagination key if more remain.
task.cancel()

Cancels the task if queued or in progress. Updates the task in place.
task.refresh()

Refreshes the task's state in place.
Fields

agent_task_id, project_id, status (TaskStatus), created_at, last_updated_at, percent_complete, description, file_name, output_summary.
Event

An Event represents one step Aristotle took during a task: a build, a file edit, a search, a message. Events are streamed by task.wait_for_completion and task.show, and listed by task.get_events.
Fields

event_id, agent_task_id, event_type (EventType), created_at, content, file_path, explanation, status.
ProjectStatus
python

class ProjectStatus(IntEnum):
    UNKNOWN = 0
    RUNNING = 1
    IDLE = 2

RUNNING indicates at least one active task. IDLE indicates no task is currently running. UNKNOWN indicates a server response this SDK version does not recognize; upgrade aristotlelib.
TaskStatus
python

class TaskStatus(Enum):
    UNKNOWN = "UNKNOWN"
    QUEUED = "QUEUED"
    IN_PROGRESS = "IN_PROGRESS"
    COMPLETE = "COMPLETE"
    COMPLETE_WITH_ERRORS = "COMPLETE_WITH_ERRORS"
    OUT_OF_BUDGET = "OUT_OF_BUDGET"
    FAILED = "FAILED"
    CANCELED = "CANCELED"

COMPLETE_WITH_ERRORS signals partial progress that did not fully satisfy the prompt. OUT_OF_BUDGET signals compute exhaustion; partial results are typically available. Both are resumable via project.ask().
EventType
python

class EventType(SafeIntEnum):
    UNKNOWN = 0
    MESSAGE = 1
    BUILDING = 2
    THINKING = 3
    EDITING_FILE = 4
    SEARCHING_LOCAL = 5
    RUNNING_COMMAND = 6
    PROVING = 7
    READING_FILES = 8
    REVIEWING = 9
    FINISHED = 10
    ERROR = 11
    READING_LEAN = 12
    SEARCHING_EXTERNAL = 13
    RUNNING_LEAN = 14

Errors

Network and API failures raise AristotleAPIError. When the failure originates from an HTTP response, the exception's status_code attribute is set.
python

from aristotlelib import AristotleAPIError

try:
    project = await Project.create(prompt="My prompt")
except AristotleAPIError as e:
    print(f"API error (status {e.status_code}): {e}")


## Toolchain Requirements
Toolchain and Requirements
Lean and Mathlib Versions

Aristotle runs on fixed versions of Lean and Mathlib:

Lean Toolchain: leanprover/lean4:v4.28.0

Mathlib: 8f9d9cff6bd728b17a24e163c9402775d9e6a365

Compatibility

Your project can use different versions, but Aristotle may encounter issues if there are breaking changes between your version and the versions above.

For best results, match your lean-toolchain file to leanprover/lean4:v4.28.0.
Project Requirements

Your Lean project should include:

    A lakefile.toml (or lakefile.lean) configuration file
    A lean-toolchain file
    Proper import structure

The SDK automatically detects your project root, validates file paths, resolves imports to include dependencies, and handles file size limits (100 MB max per file).

## Tips and Tricks
Tips and Tricks
Suppressing aesop Warnings
The following warning does not indicate a problem with your proof: aesop: failed to prove the goal after exhaustive search

This is expected behavior when aesop is used as a non-terminal tactic (i.e., when other tactics follow it). To suppress it:
lean

aesop (config := { warnOnNonterminal := false })

Resuming an Incomplete Task

When a task ends in OUT_OF_BUDGET or COMPLETE_WITH_ERRORS, continue in the same project with a follow-up prompt. Aristotle keeps the project context, so you can ask it to finish the remaining work directly:

aristotle ask <project-id> "Continue from the partial proof and finish the remaining sorries"

Waiting for a Project

submit and formalize accept --wait, which blocks until the task ends with a live progress display:

aristotle submit "Prove that there are infinitely many primes" --wait

To wait on a project submitted without --wait, or to watch one from another shell, use show:

aristotle show <project-id>

show live-tails events on the latest task until it completes. Once it returns, retrieve the result with aristotle download <project-id> --destination output.tar.gz.

## Citing
Citing Aristotle

Citing Aristotle helps others reproduce and extend your results, helps readers follow your methodology, and helps people discover Aristotle. If Aristotle contributed to your work, consider a citation — though it's never required.
GitHub

If Aristotle contributed to your PR, you can mention it on GitHub.

Tag Aristotle on PRs and Issues — mention @Aristotle-Harmonic in pull requests or issues where Aristotle contributed.

Co-author commits — if Aristotle significantly contributed to your code, consider making Aristotle a coauthor by adding this to the end of your commit message:

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Papers and Preprints

If Aristotle helped produce or verify results you are publishing or presenting, consider citing the Aristotle Technical Report.

    Tudor Achim et al. "Aristotle: IMO-level Automated Theorem Proving." arXiv preprint 2510.01346, 2025.

BibTeX:
bibtex

@misc{achim2025aristotleimolevelautomatedtheorem,
  title         = {Aristotle: IMO-level Automated Theorem Proving},
  author        = {Tudor Achim and Alex Best and Alberto Bietti and Kevin Der
                   and Mathïs Fédérico and Sergei Gukov
                   and Daniel Halpern-Leistner and Kirsten Henningsgard
                   and Yury Kudryashov and Alexander Meiburg
                   and Martin Michelsen and Riley Patterson
                   and Eric Rodriguez and Laura Scharff
                   and Vikram Shanker and Vladmir Sicca
                   and Hari Sowrirajan and Aidan Swope and Matyas Tamas
                   and Vlad Tenev and Jonathan Thomm
                   and Harold Williams and Lawrence Wu},
  year          = {2025},
  eprint        = {2510.01346},
  archivePrefix = {arXiv},
  primaryClass  = {cs.AI},
  url           = {https://arxiv.org/abs/2510.01346}
}

Researchers we've spoken with have said they are interested in:

    Abstract — Aristotle's key contributions and role in producing results.
    Methodology — How Aristotle fit into the project, what worked well, and what didn't.
    Supplementary materials — Prompts used, Aristotle's outputs, and other artifacts.

Other

For blog posts, talks, or other informal contexts, sharing a link to aristotle.harmonic.fun is always appreciated.
