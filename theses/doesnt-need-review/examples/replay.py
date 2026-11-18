"""Exercise the six migration reports against a current and a legacy SQL reader."""
import sqlite3

BATCH = [
    ("add", True), ("add", False), ("drop", True),
    ("drop", False), ("add", True), ("drop", True),
]


def observed_policy(change, retired):
    kind, expected_current = change
    db = sqlite3.connect(":memory:")
    try:
        db.execute("CREATE TABLE items (id INTEGER, value TEXT, legacy TEXT)")
        db.execute("INSERT INTO items VALUES (1, 'ok', 'old')")
        if kind == "add":
            db.execute("ALTER TABLE items ADD COLUMN label TEXT")
        else:
            db.execute("ALTER TABLE items DROP COLUMN legacy")
        if not expected_current:
            db.execute("UPDATE items SET value = 'broken'")
        current_ok = db.execute("SELECT value FROM items WHERE id=1").fetchone() == ("ok",)
        try:
            legacy_ok = db.execute("SELECT legacy FROM items WHERE id=1").fetchone() == ("old",)
        except sqlite3.OperationalError as error:
            if str(error) != "no such column: legacy":
                raise
            legacy_ok = False
        return current_ok, current_ok and (retired or legacy_ok)
    finally:
        db.close()


def verify():
    manual = 0
    for change in BATCH:
        tests, active_result = observed_policy(change, retired=False)
        repeated, retired_result = observed_policy(change, retired=True)
        if tests != repeated or tests != change[1]:
            raise ValueError("unstable current reader")
        disposition = None if tests and change[0] == "drop" else tests
        if (disposition is None) != (active_result != retired_result):
            raise ValueError("escalation disagrees with the two executable worlds")
        if disposition is None:
            manual += 1
        elif disposition != active_result or disposition != retired_result:
            raise ValueError("automated verdict changed the policy")
    if manual != 2:
        raise ValueError("expected two unresolved migrations")
    print(f"SQLite {sqlite3.sqlite_version} | 6 -> {manual} owner decisions | 12 database executions")


if __name__ == "__main__":
    verify()
