import pandas as pd
from graphviz import Digraph

class TreeNode:
    def __init__(self, value):
        self.value = value
        self.children = []

    def add_child(self, child_node):
        self.children.append(child_node)

def parse(user_input, start_symbol, parsingTable, n=None):
    stack = [start_symbol]
    pointer = 0
    stack_history = []
    tree_nodes = {}

    # инициализация корня дерева
    root = TreeNode(start_symbol)
    tree_nodes[start_symbol] = root
    current_node = root

    while stack:
        stack_history.append(list(stack))  # сохранение текущего состояния стека
        top = stack[-1]
        current_input = user_input[pointer] if pointer < len(user_input) else '$'

        if top == current_input:
            # совпадение с вершиной стека - прогресс в разборе
            stack.pop()  # удаление вершины стека
            pointer += 1  # переход к следующему символу строки

            # переход к следующему узлу дерева, если это возможно
            if current_node.children:
                current_node = current_node.children[-1]
        elif (top, current_input) in parsingTable:
            # найдено правило для развертывания
            production = parsingTable[(top, current_input)]
            stack.pop()  # убираем верхний элемент стека

            # добавляем элементы продукции в стек в обратном порядке
            for symbol in reversed(production):
                stack.append(symbol)

                # создаем новый узел в дереве разбора
                new_node = TreeNode(symbol)
                current_node.add_child(new_node)
                tree_nodes[symbol] = new_node

            # обновляем текущий узел дерева разбора
            if production:
                current_node = tree_nodes[production[0]]
        else:
            # ошибка разбора: невозможно применить правило
            print(f"Ошибка разбора на позиции {pointer}. Стек: {stack_history[-1]}")
            return None

        # визуализация стека до шага n
        if n is not None and len(stack_history) == n:
            visualize_stack(stack_history[n - 1], n)

    # возвращаем корень дерева разбора
    return root


def visualize_stack(stack_history, step):
    graph = Digraph(comment=f'Стек до шага {step}')
    
    # визуализация состояний стека до step
    for step_number, stack in enumerate(stack_history[:step], start=1):
        with graph.subgraph(name=f'cluster_{step_number}') as sub:
            sub.attr(label=f'Step {step_number}')
            for i, element in enumerate(stack):
                sub.node(f'step{step_number}_node{i}', label=str(element))
            
            for i in range(len(stack) - 1):
                sub.edge(f'step{step_number}_node{i}', f'step{step_number}_node{i + 1}')

    graph.render(f'стек_до_шага_{step}', view=True, format='png')


def ll1(follow, productions):
    table = {}
    for nonterminal, rules in productions.items():
        for rule in rules:
            if rule != '@':
                for terminal in first(rule, productions):
                    table[(nonterminal, terminal)] = rule
            else:
                for terminal in follow[nonterminal]:
                    table[(nonterminal, terminal)] = rule

    # вывод таблицы для проверки
    for key, value in table.items():
        print(f"{key}: {value}")
    return table

def follow(s, productions, ans):
    if len(s) != 1:
        return {}

    if s not in ans:
        ans[s] = set()

    for key in productions:
        for value in productions[key]:
            f = value.find(s)
            if f != -1:
                if f == (len(value) - 1):
                    if key != s:
                        if key in ans:
                            temp = ans[key]
                        else:
                            ans = follow(key, productions, ans)
                            temp = ans[key]
                        ans[s].update(temp)
                else:
                    first_of_next = first(value[f+1:], productions)
                    if '@' in first_of_next:
                        if key != s:
                            if key in ans:
                                temp = ans[key]
                            else:
                                ans = follow(key, productions, ans)
                                temp = ans[key]
                            ans[s].update(temp)
                            ans[s].update(first_of_next - {'@'})
                    else:
                        ans[s].update(first_of_next)

    return ans

def first(s, productions):
    c = s[0]
    ans = set()
    if c.isupper():
        for st in productions[c]:
            if st == '@':
                if len(s) != 1:
                    ans = ans.union(first(s[1:], productions))
                else:
                    ans = ans.union('@')
            else:
                f = first(st, productions)
                ans = ans.union(f)
    else:
        ans = ans.union(c)
    return ans