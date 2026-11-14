# XYin research and ForMathlib migration workspace

A local, configuration-driven workspace for Lean source files and existing task records. It **does not move or modify Lean files, or run Lean / Lake builds**. It has no network dependencies or third-party frontend packages.

## Open the workspace

From the repository root, run the local server with Python 3.10 or later:

```sh
python3 -B progress/server.py
```

Then open <http://127.0.0.1:8765>. The server listens only on your machine and supports saving configuration to the repository and refreshing the scan. Press Ctrl+C to stop it. If the port is in use, add `--port 8766`.

You can also double-click `index.html` to browse and edit offline. Offline changes are retained as drafts in the current browser. Export the configuration to JSON to keep a copy, then use Import to load it. **Exporting does not write back to the repository.** Browser storage is separate for different browsers and addresses; export important changes or save them through the local server.

To use an exported file as the repository configuration, replace `config.json` in this directory with it, then regenerate:

```sh
python3 -B progress/generate.py
```

This refreshes `snapshot.json` and the self-contained `index.html`. While the server is running, you can also refresh the scan from the interface.

## Discover new ForMathlib directories

**Refresh scan** and `generate.py` detect new immediate subdirectories of `XYin/ForMathlib/`, including empty directories. For example, a new `Topology/` directory receives a **ForMathlib → Topology** project and a rule matching `XYin/ForMathlib/Topology/**/*.lean`. New defaults are saved to `config.json` and included in the regenerated HTML. No Lean files or imports change.

Existing directory-wide rules are retained. When a rule is needed, discovery reuses an unambiguous matching top-level project or creates one with the directory's name. It does not create an approach or infer a proof status. New rules sit above the built-in catch-all rules in priority, but below existing manual rules and individual overrides. Existing names, descriptions, project relationships, approaches, migration records and rule order are preserved.

Each directory is recorded as already considered. Later scans do not undo your edits, restore deleted projects or rules, or remove entries when a directory disappears. Hidden directories and symbolic links are ignored. Unsupported directory names, ambiguous existing projects or a missing ForMathlib category are reported without guessing a replacement.

Unsaved interface edits are retained when new defaults arrive, including edits made while a scan is running. A matching project you have just created in the draft is reused instead of being duplicated. Undo still reverses your edits without removing defaults already saved by the scan. If older undo steps would remove a project now required by discovered rules, those steps are cleared with a notice; recent compatible steps remain available. If another window has changed the saved configuration, the scan reports a conflict and retains your draft. Save your own edits with **Save to repository** when ready.

After updating the dashboard's Python or JavaScript sources, restart an already-running local server and reload the page to use the new behaviour. Starting the server or merely opening a page does not add configuration entries; discovery runs on **Refresh scan** or when you run `generate.py`.

## Available in the first version

- Browse ForMathlib, PhD, NFIL and Others in the sidebar. PhD contains logical projects such as Foundation, Cox and Modular Curve. NFIL is initially empty.
- Add, edit and delete categories, projects, approaches and environments in configuration management. Reassign dependent entries before deleting an item; deleting configuration never deletes source files.
- Search project files, filter by approach, inspect imports and direct consumers, and select several files to change their project or approach assignments together.
- Edit approach relationships: complementary, alternative, mirror, generalisation, specialisation, equivalence within a stated scope, partial integration or unconfirmed. The two existing Modular Curve experiments are registered as complementary.
- Create ForMathlib migration items with sources, targets, stages and the downstream projects in scope. Record manual adoption confirmation separately.
- Inspect source and target references in the adoption matrix. These are calculated from module import closures; manual confirmation is not treated as a successful build.
- View historical evidence and detailed Cox ticket records, including dates, scope and AINTLIB source matches.
- Undo draft edits, import and export configuration, save locally, and detect conflicting saves from different windows. Earlier drafts and drafts from other windows are retained separately and can be viewed, exported, loaded or deleted. Deletion is rejected if another window has updated the retained draft.

## Configuration is the editable source of truth

`config.json` uses `schemaVersion: 1`:

| Field | Contents |
| --- | --- |
| `categories` | Repository categories |
| `projects` | Projects and their parents; parent and child belong to the same category |
| `approaches` | Approaches, owning projects, environments, roles and build entry points |
| `environments` | Toolchains and notes about separate environments |
| `assignments` | File path rules; the last matching rule wins |
| `overrides` | Manual file assignments, taking precedence over every rule |
| `relations` | Manually recorded relationships between approaches and their scope |
| `migrations` | Migration items, source and target files, stages, intended consumers and manual adoption confirmation |
| `discoveredForMathlibDirectories` | Optional list of directories already considered by discovery; retained so later scans respect manual edits and deletions |

Paths are relative to the repository root and use `/`. `*` matches within one path component, `**` matches across components, and `**/` can match zero components. Editing rules does not reorganise Lean files. Moving an approach to another logical project also updates the rules and individual file assignments that reference it. IDs remain stable; display names can change.

`candidate → preparing → ready → switching → complete` describes manually recorded migration stages only. Source files can remain as independent approaches. Targets must be under `XYin/ForMathlib/` and may name planned files that do not yet exist. Saving does not modify imports.

The local service accepts configuration JSON only from its own page. It uses a hash of the configuration file to prevent an older page from overwriting another page's save. If a conflict occurs, export the local draft, load the repository configuration and reconcile the changes. There is no interface for executing arbitrary commands or writing arbitrary files.

## Evidence and scope

The scanner covers `XYin/`, `XYinTest/` and the two root Lean entry points, excluding dependency directories. Source hashes and imports are static observations, not proof-completion claims. The adoption matrix counts files that import source or target modules directly or indirectly, excluding the migration's source and target files themselves. The absence of detected references does not establish the absence of a mathematical dependency.

- Cox ticket status comes from each file's `Status` entries and `tickets.json`, and includes proof and cleanup tasks. Old proof skeletons retained in the documentation are not counted as gaps in the current source.
- The ForMathlib overview is a historical report with a fixed date and scope. Newly migrated modules do not inherit its verification status.
- AINTLIB records come from a separate pinned environment. Matching source files do not replace rechecking the dependency environment and transitive axioms.
- `.mathlib-quality/` is ignored by the repository. If it is unavailable on another machine, the dashboard reports this and retains the other data.

## Files and checks

The interface sources are `web/template.html`, `web/style.css`, `web/model.js` and `web/app.js`. Do not edit the generated `index.html` directly. `generate.py` and `server.py` use only the Python standard library. Generated files remain in the repository so they can be opened directly. They contain the current machine's repository path and are not uploaded automatically.

```sh
python3 -B progress/generate.py
node --test progress/test_model.cjs progress/test_app.cjs
python3 -B -m unittest discover -s progress -p 'test_backend.py'
```

The Python tests use temporary directories. HTTP tests require a local loopback port. They do not run Lean or change the repository configuration or proof files.
