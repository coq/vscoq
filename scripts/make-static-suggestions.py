import collections
import json
import re

full_grammar = "/home/monner/Projects/coq/doc/tools/docgram/orderedGrammar"
lines = ""
with open(full_grammar, "r") as f:
    lines = f.read()
rules = lines.split("\n\n")
rule_lines = [*map(lambda x: x.split("\n"), rules)]
all_rules = {}
for name, *ls, _ in rule_lines[:-1]:
    all_rules[name[:-3]] = ls

for thing in ["command", "tactic"]:
    tactics = collections.defaultdict(list)
    for n in filter(lambda x: thing in x, all_rules.keys()):
        for line in all_rules[n]:
            rgx = r'^\| "([^"]+)"(.*)'
            m = re.search(re.compile(rgx), line)
            if m:
                if not m[1].isidentifier():
                    continue
                if not m[2]:
                    tactics[m[1]]
                else:
                    tactics[m[1]].append(m[2].strip())

    def parse(line):
        l, *comment = line.split("(*")
        comment = comment[0].strip().split()[0] if comment else None
        data = l.split()
        if not data:
            return ('', comment)
        newWords = []
        trailer = ""
        trailerStack = []
        sep = False

        for i, word in enumerate(data):
            if word in ['[', '(']:
                newWords.append(f' {word}')
                trailerStack.append(trailer)
                trailer = ''
            elif word in [']', ')']:
                if not trailerStack:
                    print(line, "failed")
                newWords.append(f' {word}{trailerStack.pop()}')
            elif word == '|':
                newWords.append(f' {word}')
            elif word == 'OPT':
                trailer = '?'
            elif word == 'LIST1':
                trailer = '+'
            elif word == 'LIST0':
                trailer = '*'
            elif word == 'SEP':
                sep = True
                pass
            elif '"' in word:
                newWord = f'`{word[1:-1]}`'
                if sep:
                    sep = False
                    # look behind: if paren, put in parens, else create parens and put in
                    if i > 0 and newWords[-1] in [' ]+', ' ]-', ' )+', ' )-']:
                        newWords[-1] = f' {newWord}{newWords[-1][:-1]}{newWords[-1][-1]}'
                    else:
                        newWords[-1] = f' ({newWords[-1][:-1]} {newWord} ){newWords[-1][-1]}'
                else:
                    newWords.append(' ' + newWord + trailer)
                    trailer = ''
            else:
                newWords.append(
                    f' *{word}*{trailer}')
                trailer = ''
        return ("".join(newWords)[1:], comment)

    def libnames(n):
        if n == 'SSR':
            return 'SSReflect'
        else:
            return f'{n} plugin'

    def describe(name):
        lines = []
        lines.append(f'### `{name}` ({thing})')
        plugins = collections.defaultdict(list)
        for line in tactics[name]:
            usage, plugin = parse(line)
            plugins[plugin].append(usage)
        if not plugins:
            lines.append('#### Usage')
            lines.append(f'| `{name}`')
            return '\n'.join(lines)
        for k in sorted(plugins, key=lambda x: x or ''):
            lines.append('#### Usage' + (f' ({libnames(k)})' if k else ''))
            for usage in sorted(plugins[k]):
                lines.append(f'| `{name}` {usage}  ')
        return '\n'.join(lines)

    kind = 22 if thing == 'command' else 1
    tt = []

    for tactic in tactics:
        tt.append({
            'label': tactic,
            'documentation': {
                'kind': 'markdown',
                'value': describe(tactic),
            },
            'kind': kind + 1,
        })

    x = ('"', '\\"')
    q = '"'
    joiner = ";\n    "
    with open(f'/home/monner/Projects/vscoq/language-server/dm/data/{thing}.ml', 'w') as f:
        f.write('(** This file is auto-generated *)\n\n')
        f.write(f'module {thing.title()} = struct\n\n')
        f.write(
            f'  let {thing}Json = [{joiner.join(map(lambda t: f"{q}{json.dumps(t).replace(*x)}{q}", tt))}]\n\n')
        f.write(
            f'  let {thing} = List.map Yojson.Safe.from_string {thing}Json\n\n')
        f.write(f'end\n')
