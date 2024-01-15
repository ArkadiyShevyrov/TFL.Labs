from grammar import parse, ll1, follow, first

def main():
    w = input("Введите строку для разбора: ")

    n = input("Введите n-ый шаг разбора для отображения стека (оставьте пустым, если не нужно): ")
    n = int(n) if n.isdigit() else None

    start = input("Введите стартовый нетерминал: ")

    print("Введите правила грамматики (введите '0' для окончания ввода):")
    productions = {}
    while True:
        rule = input()
        if rule == '0':
            break
        lhs, rhs_str = rule.split('=')
        rhs_set = set(rhs_str.split('|')) - {''}  # разделяем правую часть на две части и удаляем пустые строки
        productions[lhs] = rhs_set if lhs not in productions else productions[lhs].union(rhs_set)

    # построение таблицы LL1
    first_dict = {lhs: first(lhs, productions) for lhs in productions}
    follow_dict = {lhs: set() for lhs in productions}
    follow_dict[start] = follow_dict[start].union('$')

    for lhs in productions:
        follow_dict = follow(lhs, productions, follow_dict)

    ll1Table = ll1(follow_dict, productions)

    # вызов функции parse
    parse(w, start, ll1Table, n)

if __name__ == "__main__":
    main()
