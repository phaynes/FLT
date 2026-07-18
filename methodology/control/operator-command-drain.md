# FLT operator-command drain

This is a standing first step of every controller work-selection cycle.

1. Read the append-only operator channel at
   `/Volumes/second-store/devel/knowledge-base-mcp/mentormind/helios-projects/project/helios-control/control/operator-outbox.ndjson`.
2. Select `OperatorCommand` records for `target_project = "flt"` that have no matching
   `OperatorCommandAck`, ordered by `command_id`.
3. Refuse commands with an empty `authorized_by`; otherwise execute the directive or its referenced
   work-order under the FLT operating contract.
4. Append exactly one acknowledgement to the same channel for every attempted command:
   `consumed`, `failed`, or `refused`. Never silently drop a command.
5. Only after the pending set is empty may normal dependency-based work selection proceed.

The channel is a courier for operator-authored directions. It does not authorize a human-only T2
gate unless the command itself carries that explicit operator authorization. The drain is idempotent:
acknowledged command IDs are never re-executed.
