"""Compare SQL's native SUM with an independently merged sum-and-presence summary."""
import itertools
import sqlite3


def verify():
    db = sqlite3.connect(":memory:")
    try:
        db.execute("CREATE TABLE shard (position INTEGER, sample INTEGER)")
        runs = 0
        for size in range(6):
            for rows in itertools.product((None, -1, 0, 2), repeat=size):
                db.execute("DELETE FROM shard")
                db.executemany("INSERT INTO shard VALUES (?,?)", enumerate(rows))
                expected, = db.execute("SELECT SUM(sample) FROM shard").fetchone()
                for split in range(size + 1):
                    parts = [db.execute(f"SELECT COALESCE(SUM(sample),0), COUNT(sample)>0 "
                                        f"FROM shard WHERE position {op} ?", (split,)).fetchone()
                             for op in ("<", ">=")]
                    actual = sum(s for s, _ in parts) if any(p for _, p in parts) else None
                    if actual != expected:
                        raise ValueError((rows, split, actual, expected))
                    runs += 1
        print(f"SQLite {sqlite3.sqlite_version}: {runs} split/merge comparisons matched native SUM")
    finally:
        db.close()


if __name__ == "__main__":
    verify()
