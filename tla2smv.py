


class ITEM:
    CONDITION = 'condition'
    ACTION = 'action'
    CLAUSE = 'clause'

    def __init__(self, type):
        self.type = type
        # k - v
        self.key = None
        self.value = None
        # or a clause
        self.clause = None

class CLAUSE:
    AND = '/\\'
    OR = '\\/'

    def __init__(self, pre):
        self.pre = pre
        self.op = None
        self.items = []

class Meta_State:
    def __init__(self, name):
        self.name = name
        self.clause = CLAUSE(None)


class TLA:
    NEWLINE = 0
    #COMMA = 1
    VARS = 2
    BRACKET = 3
    CASE = 4
    META = 5

    def __init__(self, path):
        self.EXTENDS = []
        self.VARIABLES= []
        self.CONSTANT = {}
        self.state_stack = []
        self.meta_states = {}
        self.meta_states_str = {}
        self.last_meat_name = None
        self.state = TLA.NEWLINE

        with open(path, 'r') as f:
            for line in f.readlines():
                self.feed(line)


        def get_ops_sentence(line):
            ops = []
            start = 0
            for i, c in enumerate(line):
                if c == '/' and line[i+1] == '\\':
                    ops.append(CLAUSE.AND)
                    end = i + 2
                elif c == '\\' and line[i+1] == '/':
                    ops.append(CLAUSE.OR)
                    start = i + 2
            sentence = line[start:].strip()
            return ops, sentence


        for k, v in self.meta_states_str.items():
            self.meta_states[k] = Meta_State(k)
            root = self.meta_states[k].clause
            curr_clause = root
            for i, line in enumerate(v):
                ops, sentence = get_ops_sentence()
                if i == 0:
                    for op in ops[:-1]:
                        curr_clause.op = op
                        curr_clause.item = ITEM(ITEM.CLAUSE)
                        curr_clause.item.clause = CLAUSE(self)
                        curr_clause.

                for



        print(self.EXTENDS)
        print(self.VARIABLES)
        print(self.CONSTANT)
        print(self.meta_states_str['UE_reboot'])

        # self.meta_state_str = self.get_meta_state_str(content)









    def feed(self, line: str): # get vars, constant and extends
        line = line.strip()
        if not line: return
        if line.startswith('--'): return
        if line.startswith('=='): return
        if self.state == TLA.NEWLINE:
            if line.startswith('EXTENDS'):
                line = line[line.index(' ') + 1:]
                for extend in line.split(','):
                    self.EXTENDS.append(extend.strip())
            elif line.startswith('VARIABLES'):
                self.state_stack.append(self.state)
                self.state = TLA.VARS
            elif line.endswith('=='):
                self.state_stack.append(self.state)
                self.state = TLA.META
                name = line[:-2].strip()
                self.meta_states_str[name] = []
                self.last_meat_name = name
            elif line.startswith('/\\'):
                assert False
            elif line.startswith('\\/'):
                assert False
            elif line.startswith('\\E'):
                assert False
            elif line.startswith('['):
                self.state_stack.append(self.state)
                self.state = TLA.BRACKET
            elif line.startswith('CASE'):
                self.state_stack.append(self.state)
                self.state = TLA.CASE
            else:
                assert '==' in line, line  # Constant Set
                name, value = line.split('==')[0].strip(), line.split('==')[1].strip()
                if value.startswith('UNION'):
                    self.CONSTANT[name] = '{'
                    value = value[5:].strip()
                    value = value[1:-1]
                    for c in value.split(','):
                        self.CONSTANT[name] += self.CONSTANT[c.strip()][1:-1]
                        if self.CONSTANT[c.strip()][1:-1] not in ['']:
                            self.CONSTANT[name] += ', '
                    if self.CONSTANT[name].endswith(', '):
                        self.CONSTANT[name] = self.CONSTANT[name][:-2]
                    self.CONSTANT[name] += '}'
                else:
                    self.CONSTANT[name] = value

        elif self.state == TLA.VARS:
            for var in line.split(','):
                if var.strip():
                    self.VARIABLES.append(var.strip())
            if not line.endswith(','):
                self.state = self.state_stack.pop()
        elif self.state == TLA.BRACKET:
            if line.endswith(']'):
                self.state = self.state_stack.pop()
        elif self.state == TLA.META:
            if line.endswith('=='):
                self.state_stack.append(self.state)
                self.state = TLA.META
                name = line[:-2].strip()
                self.meta_states_str[name] = []
                self.last_meat_name = name
            else:
                self.meta_states_str[self.last_meat_name].append(line)




if __name__ == '__main__':
    tla = TLA('ENL/ENL_Model_auto.tla')