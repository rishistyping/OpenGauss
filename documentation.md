# OpenGauss Repository Documentation

This file is a retrieval-oriented context pack for ML systems and developers working on the `OpenGauss` repository.

Use this document as a high-signal summary first. Treat source files as the final authority when making code changes.

## Identity

- Repository name: `OpenGauss`
- Python package name: `gauss-agent`
- Current branch: `one-postulate`
- Primary product: a project-scoped Lean workflow orchestrator that exposes managed proving and formalization workflows through the `gauss` CLI
- Repository lineage: forked from `nousresearch/hermes-agent`, then narrowed and repurposed for Lean workflow orchestration

## Branch-Specific Summary: `one-postulate`

Compared with `main`, this branch adds a phase-1 Lean formalization surface plus the supporting paper and blueprint assets:

- `OnePostulate.lean`
- `OnePostulate/`
- `blueprint/src/content.tex`
- `paper/one-postulate.tex`
- `paper/one-postulate.pdf`
- `paper/.gitkeep`

Important branch fact:

- The `one-postulate` branch still does not change the OpenGauss Python runtime codepath relative to `main`.
- The branch-specific implementation work is concentrated in the Lean files under `OnePostulate/`.
- The imported phase-1 Lean surface stops at `OnePostulate.Selection`.
- `OnePostulate.ClassificationDerivation` remains deferred and unimported from `OnePostulate.lean`.
- If a task is about the branch-specific formalization content, the likely targets are `OnePostulate/`, `blueprint/src/content.tex`, and `paper/one-postulate.tex`.

### One-Postulate Paper Summary

The paper argues that Einstein's second postulate in special relativity is unnecessary as a foundational input. The core claim is:

- The relativity principle alone determines a one-parameter family of kinematic algebras.
- The algebra's Killing form fixes the physically valid branch.
- `kappa > 0` yields Lorentzian structure, non-degenerate metric structure, and a finite real invariant speed.
- `kappa = 0` is Galilean and degenerate on the boost sector.
- `kappa < 0` is Euclidean and does not support causal structure.
- Observation calibrates the value of the invariant speed, but the existence of such a speed is claimed to follow from algebraic structure alone.

Practical note:

- `paper/one-postulate.tex` is the editable source.
- `paper/one-postulate.pdf` is the built artifact.

## OnePostulate Phase-1 Theorem Map

- Bracket table: `OnePostulate.kinematic_bracket_table`
  Maps the paper's homogeneous commutator table for `J_i` and `K_i`.
- Jacobi: `OnePostulate.kinematic_bracket_jacobi`
  Packages the Jacobi identity for the six-dimensional phase-1 kinematic algebra.
- Killing form: `OnePostulate.killing_form_diag`, `OnePostulate.boost_killing_form_eq`, `OnePostulate.boost_killing_nondegenerate_iff_kappa_ne_zero`
  Covers the explicit diagonal Killing form computation and the boost-sector nondegeneracy split by `κ`.
- Zero-branch conformal-only surface: `OnePostulate.boost_invariant_form_scalar`, `OnePostulate.killing_restricts_to_metric`, `OnePostulate.velocityMetricMatrix_at_zero`
  This is the current phase-1 Lean surface for the paper's "conformal class only at κ = 0" claim; it is represented by these combined lemmas rather than a stronger dedicated theorem.
- Spacetime metric invariance: `OnePostulate.spacetime_metric_invariant`
  Formalizes invariance of the explicit spacetime metric under the matrix generators.
- Positive-branch Lorentz congruence: `OnePostulate.spacetime_metric_congruent_stdLorentz_of_kappa_pos`
  Gives the explicit congruence to standard Lorentz signature when `κ > 0`.
- Zero-branch reducibility: `OnePostulate.reducible_of_kappa_zero`, `OnePostulate.spacetime_metric_degenerate_of_kappa_zero`
  Captures the invariant time line and metric degeneracy at `κ = 0`.
- Final `κ < 0 / κ = 0 / κ > 0` trichotomy: `OnePostulate.phase1_selection_summary`
  Packages the phase-1 branch consequences for the Euclidean, Galilean, and Lorentzian cases.

## What This Repository Actually Is

This repository is primarily a Python application, not a Lean library and not a paper-only repo.

Its main job is to:

- detect or create an active Lean project
- launch managed backend child agents for Lean workflows
- forward workflow commands into `lean4-skills`
- track detached background workflow sessions
- expose that functionality through a CLI, messaging gateway, and ACP editor integration

The core user-facing workflow commands are:

- `/prove`
- `/draft`
- `/autoprove`
- `/formalize`
- `/autoformalize`
- `/swarm`

These are described in `README.md` and implemented through the Gauss CLI and swarm management layers.

## Primary Entrypoints

Package entrypoints are defined in `pyproject.toml`:

- `gauss` -> `gauss_cli.main:main`
- `gauss-agent` -> `run_agent:main`
- `gauss-acp` -> `acp_adapter.entry:main`

Interpretation:

- `gauss` is the main user entrypoint.
- `gauss-agent` exposes the lower-level agent runner.
- `gauss-acp` is the editor/IDE integration entrypoint.

## High-Level Architecture

### 1. Core Agent Runtime

Primary files:

- `run_agent.py`
- `agent/prompt_builder.py`
- `agent/context_compressor.py`
- `agent/prompt_caching.py`
- `agent/model_metadata.py`
- `gauss_state.py`

Responsibilities:

- conversation loop
- model calls
- tool-call execution
- context compression
- prompt assembly
- session persistence

Important facts:

- `AIAgent` in `run_agent.py` is the core engine.
- The main loop lives in `run_conversation()`.
- Prompt caching stability matters. The system prompt is intentionally stable across a session except when compression or explicit rebuild paths apply.
- Session persistence uses SQLite with FTS-backed message search in `gauss_state.py`.

### 2. Tool System

Primary files:

- `model_tools.py`
- `toolsets.py`
- `tools/registry.py`
- `tools/file_tools.py`
- `tools/web_tools.py`
- `tools/browser_tool.py`
- `tools/terminal_tool.py`
- `tools/process_registry.py`
- `tools/approval.py`
- `tools/mcp_tool.py`
- `tools/delegate_tool.py`
- `tools/environments/`

Responsibilities:

- tool registration
- tool schema exposure to the model
- tool dispatch
- file/web/browser execution
- terminal sandbox execution
- dangerous-command approval
- background process tracking
- optional MCP server integration
- subagent delegation

Important facts:

- Tool files self-register through `tools/registry.py`.
- `model_tools.py` imports tool modules to trigger registration, then exposes definitions and dispatch.
- OpenGauss intentionally keeps the default active tool surface narrow in `toolsets.py`: mostly file, web, and browser.
- The repo contains more tool implementations than the default OpenGauss runtime actively exposes.

### 3. CLI Surface

Primary files:

- `gauss_cli/main.py`
- `cli.py`
- `gauss_cli/commands.py`
- `gauss_cli/config.py`
- `gauss_cli/setup.py`
- `gauss_cli/auth.py`
- `gauss_cli/models.py`
- `gauss_cli/skin_engine.py`
- `agent/display.py`

Responsibilities:

- argparse-based top-level CLI
- interactive prompt_toolkit REPL
- slash-command routing
- setup and auth flows
- provider and model selection
- persistent config
- visual skinning

Important facts:

- `gauss_cli/main.py` is the top-level CLI router.
- `cli.py` owns the interactive REPL.
- Slash commands are defined in `gauss_cli/commands.py` but handled in `cli.py`.
- Config loading is split between `cli.py` and `gauss_cli/config.py`. This is a real maintenance hazard and a frequent source of confusion.

### 4. OpenGauss Lean Workflow Layer

Primary files:

- `gauss_cli/project.py`
- `gauss_cli/autoformalize.py`
- `swarm_manager.py`
- `README.md`

Responsibilities:

- active project discovery and registration
- workflow request resolution
- backend session launching
- detached workflow tracking and attachment

Important facts:

- OpenGauss is project-scoped. It expects an active Lean project.
- Managed workflows run in the active project root.
- Swarm tracking is a distinct layer, not just generic background processing.

### 5. Messaging, ACP, and Scheduling

Primary files:

- `gateway/run.py`
- `gateway/session.py`
- `gateway/platforms/`
- `acp_adapter/entry.py`
- `acp_adapter/server.py`
- `acp_adapter/session.py`
- `cron/jobs.py`
- `cron/scheduler.py`

Responsibilities:

- messaging platform integration
- cross-platform session routing
- editor protocol integration
- scheduled job execution

Important facts:

- `gateway/run.py` is a substantial orchestrator, not a thin wrapper.
- ACP integration is a separate subsystem with its own session management.
- Cron execution is designed to run independently of the gateway process.

### 6. Evaluation and Offline/Batch Systems

Primary files:

- `batch_runner.py`
- `mini_swe_runner.py`
- `trajectory_compressor.py`
- `environments/`

Responsibilities:

- batch evaluation
- trajectory generation/compression
- RL/evaluation tooling

Important facts:

- These files are not the main user-facing workflow path.
- They matter for offline experiments, benchmarks, and training/eval infrastructure.

## Repository Areas That Are Secondary to the Main Runtime

These directories exist, but they are not the first place to look for core workflow behavior:

- `skills/`
- `optional-skills/`
- `website/`
- `landingpage/`
- `docs/`
- `assets/`

These may still matter for specific tasks, especially skills and docs, but they are not the runtime core.

## Lean-Specific Artifacts in This Repo

The repository also contains Lean-related files at the top level, including:

- `Main.lean`
- `GaussProofSandbox.lean`
- `GaussProofSandbox/`
- `lakefile.toml`
- `lean-toolchain`

Interpretation:

- This repo now includes Lean scaffold content in addition to the Python application.
- The main product logic is still Python-first.
- If a task is about CLI/runtime behavior, start in Python files, not Lean files.
- If a task is about the proof sandbox or Lean project bootstrapping, inspect the Lean files and project scaffold.

## Current Development Environment Assumptions

From `AGENTS.md`:

- Always activate the virtual environment before running Python:
  - `source .venv/bin/activate`
- User config lives in:
  - `~/.gauss/config.yaml`
  - `~/.gauss/.env`

## Common Commands

### Install / Start

- `./scripts/install.sh`
- `gauss`
- `gauss update`

### Tests

- `source .venv/bin/activate`
- `python -m pytest tests/ -q`
- `python -m pytest tests/test_model_tools.py -q`
- `python -m pytest tests/test_cli_init.py -q`
- `python -m pytest tests/gateway/ -q`
- `python -m pytest tests/tools/ -q`

## Key Constraints and Invariants

These are important when changing the code:

- Prompt caching must not be broken by mid-session prompt or toolset churn.
- Tool registration happens at import time through the registry pattern.
- Some tools are intercepted by the agent loop rather than dispatched like normal tools.
- Background terminal processes are tracked through `tools/process_registry.py`.
- Dangerous command approval is centralized in `tools/approval.py`.
- The CLI config path is split across multiple loaders.
- Tests must not write to the real `~/.gauss/`; the test suite isolates `GAUSS_HOME`.

## Known Pitfalls

Known or documented footguns:

- `model_tools._last_resolved_tool_names` is process-global and can create surprising behavior around delegation/subagents.
- `cli.py` and `gauss_cli/config.py` are related but not identical config systems.
- `simple_term_menu` is explicitly discouraged for interactive menus.
- Spinner/display code should not rely on `\033[K` erase-to-end-of-line behavior.
- Not every tool file under `tools/` is part of the default OpenGauss active tool surface.

## Recommended File-First Navigation

If the task is about:

- general agent loop -> `run_agent.py`
- prompt construction or compression -> `agent/`
- tool dispatch -> `model_tools.py`, `toolsets.py`, `tools/registry.py`
- file/web/browser tools -> `tools/file_tools.py`, `tools/web_tools.py`, `tools/browser_tool.py`
- CLI behavior -> `gauss_cli/main.py`, `cli.py`, `gauss_cli/commands.py`
- config/auth/models -> `gauss_cli/config.py`, `gauss_cli/auth.py`, `gauss_cli/models.py`
- Lean project/workflow orchestration -> `gauss_cli/project.py`, `gauss_cli/autoformalize.py`, `swarm_manager.py`
- messaging integration -> `gateway/run.py`, `gateway/session.py`, `gateway/platforms/`
- ACP/editor integration -> `acp_adapter/entry.py`, `acp_adapter/server.py`, `acp_adapter/session.py`
- scheduled jobs -> `cron/jobs.py`, `cron/scheduler.py`
- offline evaluation -> `batch_runner.py`, `mini_swe_runner.py`, `environments/`
- branch-specific paper work -> `paper/one-postulate.tex`

## Retrieval Keywords

Useful terms for semantic retrieval:

- OpenGauss
- gauss-agent
- Lean workflow orchestrator
- autoformalization
- prove formalize autoprove autoformalize draft
- swarm manager
- project-scoped Lean sessions
- tool registry
- prompt caching
- ACP adapter
- gateway runner
- cron scheduler
- one-postulate
- Killing form
- relativity principle
- invariant speed

## Bottom Line

For this branch:

- The main product remains the OpenGauss Python runtime and Lean workflow orchestrator.
- The branch-specific additions are the `OnePostulate` Lean library, the declaration ledger in `blueprint/src/content.tex`, and the `paper/one-postulate.*` assets.
- If future work is about runtime behavior, start in the Python architecture files.
- If future work is about the phase-1 formalization, start in `OnePostulate/`.
- If future work is about the paper narrative or declaration ledger, start in `paper/one-postulate.tex` and `blueprint/src/content.tex`.
