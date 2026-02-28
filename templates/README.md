# Resource Registry Template

Portable template for bootstrapping a new project's resource registry.

## Contents

| File | Purpose |
|------|---------|
| `resource_registry.json` | 35 generic + 6 conditional resource entries with fresh UUIDs |
| `backend_schema.json` | Backend schema template (processors, endpoints, services, etc.) |
| `frontend_schema.json` | Frontend schema template (modules, components, data loaders, etc.) |
| `middleware_schema.json` | Middleware schema template (interceptors, execution patterns, etc.) |
| `shared_objects_schema.json` | Shared objects schema template (utilities, types, transformers, etc.) |

## Quick Start

1. Copy the template files into your project:
   ```bash
   cp specs/templates/resource_registry.json specs/schemas/resource_registry.json
   cp specs/templates/*_schema.json specs/schemas/
   ```

2. The 35 generic resources are ready to use immediately.

3. Activate conditional resources as needed (see below).

4. Add project-specific resources with new UUIDs.

## Conditional Resources

Six resources live in the `conditional_resources` section. To activate one, move its entry from `conditional_resources` into `resources`:

| UUID | Name | Activate when... |
|------|------|-----------------|
| `cfg-t5h9` | security | Project requires authentication/authorization |
| `cfg-u2k4` | caching | Project uses caching strategies |
| `cfg-v8l7` | internationalization | Project supports multiple locales |
| `cfg-w4n3` | documentation | Project uses generated documentation |
| `fs-x7p6` | tla_artifact_store | Project uses TLA+ formal verification |
| `fs-y3q2` | plan_artifact_store | Project uses plan-driven code generation |

## Adding Project-Specific Resources

For resources unique to your project (CLI tools, project detectors, custom stores):

1. Choose the appropriate schema prefix (`db`, `fs`, `ui`, `mq`, `api`, `cfg`).
2. Generate a 4-character base36 suffix (characters: `0-9`, `a-z`).
3. Verify the UUID doesn't collide with existing entries.
4. Add the entry to the `resources` section.

### UUID Format

```
<prefix>-<suffix>
  |         |
  |         +-- 4 alphanumeric chars (base36: 0-9, a-z)
  +------------ 2-3 lowercase letters (schema code)
```

Prefixes: `db` (database), `fs` (filesystem), `ui` (ui_state), `mq` (message_queue), `api` (external_api), `cfg` (configuration).

### Generating a Suffix

```bash
# Generate a random 4-char base36 suffix
python3 -c "import random, string; print(''.join(random.choices(string.ascii_lowercase + string.digits, k=4)))"
```

## Summary Counts

Update the `summary` section after modifying the registry to keep counts accurate. The template ships with:

- **35** generic resources (in `resources`)
- **6** conditional resources (in `conditional_resources`)
- **0** project-specific resources (add your own)
