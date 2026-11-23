#!/usr/bin/env bash
# Build the consolidated monorepo from local full clones of every clpi/software-* repo.
# Usage: build.sh SRC_DIR OUT_DIR
# SRC_DIR holds one clone per repo (all remote branches fetched, PR heads under refs/pr/*).
# Every repo lands verbatim under theses/<name>/ (name = repo minus "software-"), with
# full history rewritten by git filter-repo. Default branch is merged into main; every
# other branch and PR head is kept as archive/<name>/<ref>. Nothing is edited or dropped.
set -euo pipefail
SRC=$(cd "$1" && pwd); OUT=$2
rm -rf "$OUT"; mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
STAGE="$OUT.stage"; rm -rf "$STAGE"; mkdir -p "$STAGE"
git init -q -b main "$OUT/repo"
cd "$OUT/repo"
git config user.name "consolidation"; git config user.email "consolidation@localhost"
export GIT_AUTHOR_DATE="2026-11-23T00:00:00Z" GIT_COMMITTER_DATE="2026-11-23T00:00:00Z"
git commit -q --allow-empty -m "Start consolidated software repo"
mkdir -p "$OUT/maps"
for d in $(ls "$SRC" | sort); do
  name=${d#software-}
  src="$SRC/$d"
  def=$(git -C "$src" symbolic-ref --short refs/remotes/origin/HEAD | sed 's#^origin/##')
  defsha=$(git -C "$src" rev-parse "origin/$def")
  b="$STAGE/$name.git"
  git init -q --bare "$b"
  git -C "$b" fetch -q "$src" "+refs/remotes/origin/*:refs/heads/*" "+refs/pr/*:refs/heads/pr/*" "+refs/tags/*:refs/tags/*"
  git -C "$b" update-ref -d refs/heads/HEAD 2>/dev/null || true
  # record every ref before rewrite
  git -C "$b" for-each-ref --format='%(refname) %(objectname)' > "$OUT/maps/$name.refs-before"
  ( cd "$b" && git filter-repo --quiet --force --preserve-commit-hashes --to-subdirectory-filter "theses/$name" --tag-rename ":$name/" )
  cp "$b/filter-repo/commit-map" "$OUT/maps/$name.commit-map"
  git -C "$b" for-each-ref --format='%(refname) %(objectname)' > "$OUT/maps/$name.refs-after"
  git fetch -q "$b" "+refs/heads/*:refs/heads/archive/$name/*" "+refs/tags/*:refs/tags/*"
  git merge -q --allow-unrelated-histories --no-edit -m "Import clpi/software-$name ($def @ ${defsha:0:12}) under theses/$name" "archive/$name/$def"
  echo "$name $def $defsha" >> "$OUT/maps/imports.txt"
done
rm -rf "$STAGE"
echo "built: $(git rev-list --count HEAD) commits on main, $(git for-each-ref refs/heads/archive | wc -l) archive refs"
