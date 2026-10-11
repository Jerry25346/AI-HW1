# Adapted from PS1: Slide Puzzle Solver v1.1, Dr Loke K.S. (10/3/2017).
# Original PS1 is based on Al Sweigart and labelled Simplified BSD.
# Assignment-specific adaptations: state/operators, A*, trace and CLI.
# See IMPLEMENTATION_NOTES.md for the framework change map.
# This program is standalone and uses only the Python standard library.
from copy import deepcopy
from abc import ABCMeta, abstractmethod
import queue as Q

class Stack:
     def __init__(self):
         self.items = []
     def isEmpty(self):
         return self.items == []
     def push(self, item):
         self.items.append(item)
     def pop(self):
         return self.items.pop()
     def peek(self):
         return self.items[len(self.items)-1]
     def size(self):
         return len(self.items)
#
# Basic data structure Queue
# (Use my own Queue instead of import) 
#        
class Queue:
    def __init__(self):
        self.items = []
    def isEmpty(self):
        return self.items == []
    def add(self, item):
        self.items.insert(0,item)
    def get(self):
        return self.items.pop()
    def size(self):
        return len(self.items)


#
# Solver Class: propose moves to the Board Class 
#
#
class Solver(metaclass=ABCMeta):
    """
     ABC=Abstract base class
     Abstract Solver class that searches through the state space, called by the Board class
    """
    @abstractmethod
    def get(self):
         raise NotImplementedError()
    @abstractmethod
    def add(self):
         raise NotImplementedError()
     
class Solver1(Solver):
    """
     Concrete solver: must implement abstract methods from abstract class Solver
     uses a Queue
    """
    def __init__(self):
        self.queue=Queue()
    def get(self):
        return self.queue.get()
    def add(self,board):
        self.queue.add(board)

class Solver2(Solver):
    """
     Concrete solver: must implement abstract methods from abstract class Solver
     Uses a Stack
    """
    def __init__(self):
        self.stack=Stack()
    def get(self):
        return self.stack.pop()
    def add(self,board):
        self.stack.push(board)

# Shared adaptation of PS1 Solver3 and Board.solve, embedded in both submissions.
# The final Puzzle1.py and Puzzle2.py are standalone and need no shared module.

from dataclasses import asdict, dataclass
from pathlib import Path
from contextlib import redirect_stdout
from itertools import count
import argparse
import hashlib
import io
import json
import platform
import sys


@dataclass(frozen=True)
class SearchRecord:
    record_id: int
    state: tuple
    g: int
    h: int
    parent_record: object = None
    action: object = None

    @property
    def f(self):
        return self.g + self.h


class Solver3(Solver):
    """PS1 priority-queue solver adapted from h-only to (g+h, FIFO sequence)."""

    def __init__(self, heuristic):
        self.pq = Q.PriorityQueue()
        self.heuristic = heuristic
        self.sequence = count()

    def get(self):
        if self.pq.empty():
            return None
        return self.pq.get()[2]

    def add(self, record):
        self.pq.put((record.f, next(self.sequence), record))

    def size(self):
        return self.pq.qsize()


class SearchBoard:
    """PS1 Board.solve lifecycle with best costs, immutable parents and trace."""

    def printBoard(self, board, msg=None):
        print((msg + " " if msg else "") + self.formatState(board))

    def solve(self, start=None, verbose=True, run_id="interactive"):
        initial = tuple(self.board if start is None else start)
        if not self.isValidBoard(initial):
            raise ValueError("Invalid initial state")
        self.Solver = Solver3(self.heuristic)
        self.used = []  # PS1's expanded states; best_g now controls duplication.
        self.trace = []
        self.records = []
        state_ids = {}
        best_g = {}
        best_record = {}
        expanded_g = {}
        metrics = dict(generated=0, expanded=0, enqueued=0, improved=0,
                       pruned=0, stale=0, reopened=0, max_frontier=0,
                       unique_discovered=0, goal_dequeues=0)

        def record(state, g, parent=None, action=None):
            state = tuple(state)
            h = self.heuristic(state)
            if type(h) is not int or h < 0:
                raise ValueError("Heuristic must be a nonnegative integer")
            node = SearchRecord(len(self.records), state, g, h, parent, action)
            self.records.append(node)
            state_ids.setdefault(state, len(state_ids))
            return node

        def emit(kind, node=None, **extra):
            event = dict(run_id=run_id, event_id=len(self.trace), event=kind)
            if node is not None:
                event.update(asdict(node))
                event.update(f=node.f, state_id=state_ids[node.state],
                             display=self.formatState(node.state))
                if node.parent_record is not None:
                    parent = self.records[node.parent_record]
                    event["action_text"] = self.describeMove(parent.state, node.action)
            event.update(extra)
            self.trace.append(event)
            if verbose:
                detail = ""
                if node is not None:
                    detail = (f" R{node.record_id:04d} S{state_ids[node.state]:03d}"
                              f" {self.formatState(node.state)}"
                              f" g={node.g} h={node.h} f={node.f}"
                              f" parent={node.parent_record}")
                    if "action_text" in event:
                        detail += " action=" + event["action_text"]
                if "expansion_index" in event:
                    detail += f" expand=#{event['expansion_index']}"
                if "reference_record" in event:
                    detail += f" reference=R{event['reference_record']:04d}"
                print(f"E{event['event_id']:05d} {kind.upper():8s}{detail}")

        def enqueue(node):
            self.Solver.add(node)
            metrics["enqueued"] += 1
            metrics["max_frontier"] = max(metrics["max_frontier"], self.Solver.size())

        root = record(initial, 0)
        best_g[initial] = 0
        best_record[initial] = root.record_id
        enqueue(root)
        emit("enqueue", root, queued=True)
        goal_node = None
        while True:
            current = self.Solver.get()
            if current is None:
                emit("exhausted")
                break
            if current.g != best_g[current.state]:
                metrics["stale"] += 1
                emit("stale", current, reference_record=best_record[current.state])
                continue
            if current.state == self.goal:
                metrics["goal_dequeues"] += 1
                emit("goal", current)
                goal_node = current
                break
            if current.state in expanded_g:
                metrics["reopened"] += 1
            expanded_g[current.state] = current.g
            self.used.append(current.state)
            metrics["expanded"] += 1
            emit("expand", current, expansion_index=metrics["expanded"])
            for move in self.getMoves(current.state):
                # PS1 structure: getMoves -> makeMove -> check -> Solver.add.
                temp = self.makeMove(current.state, move)
                metrics["generated"] += 1
                child = record(temp, current.g + 1, current.record_id, tuple(move))
                previous_g = best_g.get(child.state)
                if previous_g is not None and child.g >= previous_g:
                    metrics["pruned"] += 1
                    emit("prune", child, queued=False,
                         reference_record=best_record[child.state],
                         reason="equal_or_higher_cost")
                    continue
                event_kind = "discover" if previous_g is None else "improve"
                if previous_g is not None:
                    metrics["improved"] += 1
                old_record = best_record.get(child.state)
                best_g[child.state] = child.g
                best_record[child.state] = child.record_id
                enqueue(child)
                emit(event_kind, child, queued=True, previous_record=old_record)

        path = []
        if goal_node is not None:
            current = goal_node
            while True:
                entry = asdict(current)
                entry.update(f=current.f, display=self.formatState(current.state),
                             state_id=state_ids[current.state])
                if current.parent_record is not None:
                    entry["action_text"] = self.describeMove(
                        self.records[current.parent_record].state, current.action)
                path.append(entry)
                if current.parent_record is None:
                    break
                current = self.records[current.parent_record]
            path.reverse()
        metrics["unique_discovered"] = len(best_g)
        metrics["frontier_at_stop"] = self.Solver.size()
        result = dict(run_id=run_id, puzzle=self.puzzle, parameters=self.parameters,
                      heuristic=self.heuristic_name, algorithm="A*",
                      tie_break="f then FIFO insertion sequence",
                      action_order=self.action_order, model_version="1.0",
                      initial=list(initial), goal=list(self.goal),
                      status="SOLVED" if goal_node else "NO_SOLUTION",
                      cost=goal_node.g if goal_node else None, path=path,
                      metrics=metrics, trace_events=len(self.trace))
        return result


METRIC_DEFINITIONS = {
    "generated": "Legal successor attempts, including duplicate/pruned occurrences; excludes root.",
    "expanded": "Valid dequeues for which successors are enumerated; excludes goal and stale entries.",
    "enqueued": "Queue insertions including root and improvements.",
    "improved": "Strictly cheaper paths accepted for a previously discovered state.",
    "pruned": "Generated occurrences discarded for equal or higher g.",
    "stale": "Dequeued queue entries whose g is no longer best.",
    "reopened": "Expansions of a state that was previously expanded.",
    "max_frontier": "Maximum number of queue entries, including stale entries not yet removed.",
    "unique_discovered": "Distinct states ever accepted into the queue.",
    "goal_dequeues": "Valid goal dequeues, excluded from expanded.",
    "frontier_at_stop": "Queue entries remaining after termination."
}


def print_solution(result):
    print()
    print(f"RUN: {result['run_id']}")
    print(f"PUZZLE: {result['puzzle']} | parameters={result['parameters']}")
    print(f"SEARCH: A* | heuristic={result['heuristic']} | ties=FIFO")
    print(f"STATUS: {result['status']}")
    if result["cost"] is not None:
        print(f"SOLUTION COST: {result['cost']} actions")
        for step, node in enumerate(result["path"]):
            action = node.get("action_text", "START")
            print(f"{step:02d}. {action:27s} {node['display']}"
                  f"  g={node['g']} h={node['h']} f={node['f']}")
    else:
        print("The finite frontier was exhausted without reaching the goal.")
    print("METRICS: " + json.dumps(result["metrics"], sort_keys=True))


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run_cli(board, args):
    run_id = args.run_id or board.default_run_id()
    buffer = io.StringIO()
    with redirect_stdout(buffer):
        print(f"RUN: {run_id}")
        print(f"State encoding: {board.encoding}")
        print(f"Action order: {board.action_order}")
        print("Trace: E=event, R=occurrence record, S=unique state, expand=expansion order")
        result = board.solve(verbose=not args.summary_only, run_id=run_id)
        print_solution(result)
    output = buffer.getvalue()
    if args.output:
        folder = Path(args.output)
        folder.mkdir(parents=True, exist_ok=True)
        (folder / "stdout.txt").write_text(output, encoding="utf-8")
        (folder / "result.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        (folder / "trace.jsonl").write_text(
            "".join(json.dumps(e) + "\n" for e in board.trace), encoding="utf-8")
        program = Path(__file__).resolve()
        manifest = dict(run_id=run_id, program=program.name, program_sha256=sha256(program),
                        python_version=platform.python_version(), executable=sys.executable,
                        dependencies="Python standard library only",
                        command=[sys.executable, str(program)] + sys.argv[1:],
                        state_encoding=board.encoding, metric_definitions=METRIC_DEFINITIONS,
                        result={k: result[k] for k in ("status", "cost", "parameters",
                                 "heuristic", "algorithm", "tie_break", "action_order",
                                 "model_version", "metrics")},
                        artifacts=dict(stdout="stdout.txt", result="result.json", trace="trace.jsonl"),
                        verification_status="NOT_RUN")
        sources = program.parent / "A1"
        manifest["source_sha256"] = {
            str(p.relative_to(program.parent)): sha256(p)
            for p in [sources / "A1.docx", sources / "PS1.py",
                      sources / "PS1-No-Animation.py", program.parent / "Syllabus.docx"]
            if p.exists()}
        (folder / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(output, end="")
    return result


def common_arguments(parser, heuristics, default):
    parser.add_argument("--heuristic", choices=heuristics, default=default)
    parser.add_argument("--output", help="Directory for stdout, result, trace and manifest")
    parser.add_argument("--run-id", help="Stable evidence run identifier")
    parser.add_argument("--summary-only", action="store_true", help="Print path without trace")


class Board(SearchBoard):
    """Liquid division model replacing PS1's sliding-tile Board.

    Assumptions: original vase remains usable; total volume is 24; pour until
    source empty or destination full. Full vessel order is (vase,5,11,13).
    """

    puzzle = "Liquid Division"
    encoding = "(amount_5, amount_11, amount_13); vase = 24 - sum(state)"
    action_order = "ascending source index, then ascending destination index"
    capacities = (24, 5, 11, 13)
    target = (8, 0, 8, 8)

    def __init__(self, heuristic="surplus-deficit"):
        if heuristic not in ("surplus-deficit", "misplaced", "zero"):
            raise ValueError("Unknown heuristic")
        self.parameters = dict(capacities=list(self.capacities), total=24,
                               pouring="until source empty or destination full")
        self.heuristic_name = heuristic
        self.board = (0, 0, 0)
        self.goal = (0, 8, 8)

    def default_run_id(self):
        return f"liquid_{self.heuristic_name}"

    def fullState(self, board):
        return (24 - sum(board),) + tuple(board)

    def isValidBoard(self, board):
        if not isinstance(board, (tuple, list)) or len(board) != 3:
            return False
        if any(type(v) is not int for v in board):
            return False
        return all(0 <= v <= cap for v, cap in zip(self.fullState(board), self.capacities))

    def moveError(self, board, move):
        if not self.isValidBoard(board):
            return "Invalid board state"
        if not isinstance(move, (tuple, list)) or len(move) != 2:
            return "A move must contain source and destination indices"
        i, j = move
        if type(i) is not int or type(j) is not int or not (0 <= i < 4 and 0 <= j < 4):
            return "Vessel indices must be integers in 0..3"
        if i == j:
            return "Source and destination must differ"
        full = self.fullState(board)
        if full[i] == 0:
            return "Source vessel is empty"
        if full[j] == self.capacities[j]:
            return "Destination vessel is full"
        return None

    def isValidMove(self, board, move):
        return self.moveError(board, move) is None

    def getMoves(self, board):
        if not self.isValidBoard(board):
            raise ValueError("Invalid board state")
        return [(i, j) for i in range(4) for j in range(4)
                if self.isValidMove(board, (i, j))]

    def makeMove(self, original_board, move):
        reason = self.moveError(original_board, move)
        if reason is not None:
            raise ValueError(reason)
        full = list(self.fullState(deepcopy(original_board)))
        i, j = move
        amount = min(full[i], self.capacities[j] - full[j])
        full[i] -= amount
        full[j] += amount
        return tuple(full[1:])

    def heuristic(self, board):
        if self.heuristic_name == "zero":
            return 0
        full = self.fullState(board)
        if self.heuristic_name == "misplaced":
            return (sum(x != y for x, y in zip(full, self.target)) + 1) // 2
        surplus = sum(x > y for x, y in zip(full, self.target))
        deficit = sum(x < y for x, y in zip(full, self.target))
        return max(surplus, deficit)

    def formatState(self, board):
        return str(self.fullState(board)).replace(" ", "") + " [vase,5,11,13]"

    def describeMove(self, board, move):
        full = self.fullState(board)
        i, j = move
        amount = min(full[i], self.capacities[j] - full[j])
        return f"v{i}->v{j}: {amount} oz"


def main():
    parser = argparse.ArgumentParser(description="PS1-derived A* liquid division solver")
    common_arguments(parser, ("surplus-deficit", "misplaced", "zero"), "surplus-deficit")
    args = parser.parse_args()
    run_cli(Board(args.heuristic), args)


if __name__ == "__main__":
    main()

