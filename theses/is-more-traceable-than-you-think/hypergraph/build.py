# Witness hypergraph builder, lane a.
# Reads only the frozen snapshot named by the first argument.
# Writes the canonical hypergraph to the path named by the second argument.
# The third argument names the feed mode: plain, shuffled, or duplicated.
# The build is a fold: each record contributes nodes and links into
# content addressed sets, so feed order and feed duplication cannot
# change the result. Time is carried on nodes and links but is never
# part of a content address, since arrival is not identity.

import bisect
import hashlib
import json
import random
import sys


def canon(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def address(value):
    return hashlib.sha256(canon(value).encode("utf-8")).hexdigest()


def read(path):
    with open(path, encoding="utf-8") as stream:
        return json.load(stream)


def locate(root, item):
    while root[item] != item:
        root[item] = root[root[item]]
        item = root[item]
    return item


def merge(root, left, right):
    a = locate(root, left)
    b = locate(root, right)
    if a != b:
        root[a] = b


def add(nodes, kind, fields):
    item = {"fields": fields, "kind": kind}
    key = address(item)
    if key not in nodes:
        nodes[key] = {"fields": fields, "id": key, "kind": kind}
    return key


def mark(times, key, batch):
    times.setdefault(key, set()).add(batch)


def stamp(times, key, order):
    found = times.get(key, set())
    return [{"batch": name, "index": order[name]} for name in sorted(found, key=lambda name: (order[name], name))]


def main():
    base = sys.argv[1]
    target = sys.argv[2]
    mode = sys.argv[3] if len(sys.argv) > 3 else "plain"
    feed = read(base + "/witnesses.json")
    steps = read(base + "/steps.json")["steps"]
    entries = read(base + "/accounting.json")["entries"]
    witnesses = list(feed["witnesses"])
    edges = list(feed["edges"])
    if mode == "shuffled":
        dice = random.Random(20261118)
        dice.shuffle(witnesses)
        dice.shuffle(edges)
    if mode == "duplicated":
        witnesses = witnesses + witnesses
        edges = edges + edges

    order = {}
    for index, step in enumerate(steps):
        order[step["batch"]] = index

    nodes = {}
    times = {}
    links = {}

    # Batch nodes, one per compounding step, in the recorded order.
    batchids = {}
    for index, step in enumerate(steps):
        fields = {"accounting-hash": step["accounting-hash"], "batch": step["batch"], "index": index, "step-hash": step["step-hash"]}
        key = add(nodes, "batch", fields)
        batchids[step["batch"]] = key
        mark(times, key, step["batch"])

    # Pin normalization, per the amendment in section 17.2 of the spec:
    # a shortened form that uniquely prefixes exactly one longest form
    # denotes that state; an ambiguous shortened form is left as recorded.
    pins = {}
    for record in witnesses:
        pins.setdefault(record["project"], set()).add(record["pin"])
    for record in edges:
        pins.setdefault(record["project"], set()).add(record["from"])
        pins.setdefault(record["project"], set()).add(record["to"])
    rewrite = {}
    rewrites = 0
    for project, group in pins.items():
        ranked = sorted(group)
        longest = []
        for spot, pin in enumerate(ranked):
            if spot + 1 < len(ranked) and ranked[spot + 1].startswith(pin):
                continue
            longest.append(pin)
        table = {}
        for pin in group:
            if pin in longest:
                table[pin] = pin
                continue
            at = bisect.bisect_left(longest, pin)
            found = [cand for cand in longest[at:at + 2] if cand.startswith(pin)]
            table[pin] = found[0] if len(found) == 1 else pin
            if table[pin] != pin:
                rewrites += 1
        rewrite[project] = table

    def state(project, pin):
        return rewrite[project][pin]

    # Symbol nodes attested by witness records and join records.
    projects = {}
    facts = {}
    states = {}
    venues = {}

    def projectnode(name, batch):
        if name not in projects:
            projects[name] = add(nodes, "project", {"name": name})
        mark(times, projects[name], batch)
        return projects[name]

    def factnode(project, fact, batch):
        pair = (project, fact)
        if pair not in facts:
            facts[pair] = add(nodes, "fact", {"fact": fact, "project": project})
        mark(times, facts[pair], batch)
        return facts[pair]

    def statenode(project, pin, batch):
        pair = (project, pin)
        if pair not in states:
            states[pair] = add(nodes, "state", {"pin": pin, "project": project})
        mark(times, states[pair], batch)
        return states[pair]

    def venuenode(name, batch):
        if name not in venues:
            venues[name] = add(nodes, "venue", {"name": name})
        mark(times, venues[name], batch)
        return venues[name]

    # Witness nodes. Identity is the source locator plus project, pin,
    # and fact name; the node is identity plus value, so one identity
    # with two values is two witnesses. The batch is time, not identity.
    seen = {}
    for record in witnesses:
        fields = {
            "contract": record["contract"],
            "digests": record["digests"],
            "fact": record["fact"],
            "grade": record["grade"],
            "host": record["host"],
            "note": record["note"],
            "pin": record["pin"],
            "project": record["project"],
            "range": record["range"],
            "source": record["source"],
            "state": state(record["project"], record["pin"]),
            "value": record["value"],
        }
        key = add(nodes, "witness", fields)
        mark(times, key, record["batch"])
        seen[key] = record
        projectnode(record["project"], record["batch"])
        factnode(record["project"], record["fact"], record["batch"])
        statenode(record["project"], state(record["project"], record["pin"]), record["batch"])
        if record["host"] is not None:
            venuenode(record["host"], record["batch"])

    # Join relations. A transition record joins its endpoints for every
    # fact (scope: the word all, as recorded in its fact field); a gate
    # proof-equal record joins its endpoints for its named fact alone.
    joins = {}
    joinlinks = {}
    joinkinds = {}
    conflicts = 0
    for record in edges:
        projectnode(record["project"], record["batch"])
        left = state(record["project"], record["from"])
        right = state(record["project"], record["to"])
        statenode(record["project"], left, record["batch"])
        statenode(record["project"], right, record["batch"])
        scope = record["fact"]
        pair = tuple(sorted((left, right)))
        tag = (record["project"], scope, pair)
        if tag in joins:
            if joinkinds[tag] != record["kind"]:
                conflicts += 1
            mark(times, joins[tag], record["batch"])
            mark(times, joinlinks[tag], record["batch"])
            continue
        fields = {"from": pair[0], "kind": record["kind"], "project": record["project"], "scope": scope, "to": pair[1]}
        key = add(nodes, "join", fields)
        mark(times, key, record["batch"])
        joins[tag] = key
        joinkinds[tag] = record["kind"]
        premises = sorted((states[(record["project"], left)], states[(record["project"], right)]))
        item = {"conclusion": key, "fields": {"kind": record["kind"], "project": record["project"], "scope": scope}, "kind": "join", "premises": premises}
        link = address(item)
        links[link] = {"conclusion": key, "fields": item["fields"], "id": link, "kind": "join", "premises": premises}
        joinlinks[tag] = link
        mark(times, link, record["batch"])

    # Class formation, per section 17.4 of the spec. Components are
    # computed over every state of the project, so connectivity flows
    # through states carrying no witness for the fact; the members of
    # a class are the component states that carry a witness for it.
    transitions = {}
    gates = {}
    for (project, scope, pair), node in joins.items():
        if scope == "all":
            transitions.setdefault(project, []).append(pair)
        else:
            gates.setdefault((project, scope), []).append(pair)
    carrying = {}
    for key, record in seen.items():
        spot = (record["project"], record["fact"], state(record["project"], record["pin"]))
        carrying.setdefault(spot, []).append(key)
    byfact = {}
    for (project, fact, pin) in carrying:
        byfact.setdefault((project, fact), set()).add(pin)
    entrymap = {}
    for entry in entries:
        tag = (entry["project"], entry["fact"], entry["class"])
        entrymap.setdefault(tag, []).append(address(entry))
    classes = 0
    matched = 0
    for (project, fact), members in sorted(byfact.items()):
        root = {}
        for pin in pins[project]:
            root[state(project, pin)] = state(project, pin)
        for pair in transitions.get(project, []):
            merge(root, pair[0], pair[1])
        for pair in gates.get((project, fact), []):
            merge(root, pair[0], pair[1])
        groups = {}
        for pin in members:
            groups.setdefault(locate(root, pin), set()).add(pin)
        for spot, group in groups.items():
            pinsin = sorted(group)
            label = ",".join(pinsin)
            found = sorted(entrymap.get((project, fact, label), []))
            if found:
                matched += 1
            fields = {"entries": found, "fact": fact, "label": label, "members": pinsin, "project": project}
            key = add(nodes, "class", fields)
            classes += 1
            premises = []
            for pin in pinsin:
                for wit in carrying[(project, fact, pin)]:
                    premises.append(wit)
                    mark(times, key, seen[wit]["batch"])
            premises = sorted(set(premises))
            item = {"conclusion": key, "fields": {"entries": found, "fact": fact, "project": project}, "kind": "derivation", "premises": premises}
            link = address(item)
            links[link] = {"conclusion": key, "fields": item["fields"], "id": link, "kind": "derivation", "premises": premises}
            for wit in premises:
                for moment in stamp(times, wit, order):
                    mark(times, link, moment["batch"])
                    mark(times, key, moment["batch"])

    # Boundary links. A witness whose fact names an execution is a
    # foreign outcome witnessed through the runner envelope, per
    # section 18.6 of the spec: premises are its envelope parts
    # (procedure from its contract, else its fact name; its state;
    # its venue where one is recorded) and the grain is envelope.
    procedures = {}
    boundary = 0
    for key, record in seen.items():
        if not record["fact"].startswith("execution:"):
            continue
        text = record["contract"] if record["contract"] else record["fact"]
        if text not in procedures:
            procedures[text] = add(nodes, "procedure", {"text": text})
        mark(times, procedures[text], record["batch"])
        premises = [procedures[text], states[(record["project"], state(record["project"], record["pin"]))]]
        if record["host"] is not None:
            premises.append(venues[record["host"]])
        premises = sorted(set(premises))
        item = {"conclusion": key, "fields": {"grain": "envelope"}, "kind": "boundary", "premises": premises}
        link = address(item)
        links[link] = {"conclusion": key, "fields": item["fields"], "id": link, "kind": "boundary", "premises": premises}
        mark(times, link, record["batch"])
        boundary += 1

    out = {"edges": [], "nodes": []}
    for key in sorted(nodes):
        node = nodes[key]
        out["nodes"].append({"fields": node["fields"], "id": key, "kind": node["kind"], "time": stamp(times, key, order)})
    for key in sorted(links):
        link = links[key]
        out["edges"].append({"conclusion": link["conclusion"], "fields": link["fields"], "id": key, "kind": link["kind"], "premises": link["premises"], "time": stamp(times, key, order)})
    with open(target, "w", encoding="utf-8") as stream:
        stream.write(canon(out) + "\n")

    counts = {}
    for node in out["nodes"]:
        counts[node["kind"]] = counts.get(node["kind"], 0) + 1
    kinds = {}
    for link in out["edges"]:
        kinds[link["kind"]] = kinds.get(link["kind"], 0) + 1
    stats = {"boundary": boundary, "classes": classes, "conflicts": conflicts, "hash": address(out), "kinds": kinds, "matched": matched, "nodes": counts, "rewrites": rewrites}
    print(canon(stats))


if __name__ == "__main__":
    main()
