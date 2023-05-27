# Generate partial-instance description 

from itertools import combinations
from typing import TypeVar

n: int = 7
quotas: list[tuple[str, int]] = [('A', 1), ('B', 3), ('C', 3)]
start_deck: list[int] = list(range(1, n+1))

def pick_from(cards: list[int], todo: list[tuple[str, int]]) -> list[dict[str, list[str]]]: 
    if len(todo) < 1: return [dict()]
    next_person = todo[0][0]
    next_draw = todo[0][1]
    if len(cards) < next_draw: 
        raise ValueError(f"insufficient cards remaining: {next_draw} from {cards}")
    
    picks: list[tuple[int, ...]] = list(combinations(cards, next_draw))
    if len(todo) == 1: 
        return [{next_person: [str(c) for c in pick]} for pick in picks]
    return flatten([combine_for_pick(cards, todo[1:], next_person, pick) for pick in picks])

def combine_for_pick(cards: list[int], rest_todo: list[tuple[str, int]], 
                     next_person: str, pick: tuple[int]) -> list[dict[str, list[str]]]:
    return [{next_person: [str(c) for c in pick]} | next_option 
            for next_option in pick_from([c for c in cards if c not in pick], rest_todo)]

T = TypeVar('T')
def flatten(l: list[list[T]]) -> list[T]:
    return [e for subl in l for e in subl]

def atom(w: dict[str, list[str]]) -> str:
    return f'World_{"".join(w["A"])}_{"".join(w["B"])}_{"".join(w["C"])}'
def holds(w: dict[str, list[str]]) -> str:
    return ' + '.join(['+'.join([f'{k}->Card{num}' for num in w[k]]) for k in w.keys()])

if __name__ == '__main__':    
    worlds = pick_from(start_deck, quotas)
    atoms = [atom(w) for w in worlds]
    #print(f'World = {" + ".join(atoms)}')
    print(f'one sig {",".join(atoms)} extends World ')
    for w in worlds:
        print(f'{atom(w)}.holds = {holds(w)}')



