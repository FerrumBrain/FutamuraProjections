#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <numeric>
#include <regex>
#include <vector>
#include <string>
#include <stdexcept>
#include <sstream>

using namespace std;

class FlowchartLiteral;
class FlowchartLabel;
class FlowchartVariable;
class FlowchartProgramState;
class FlowchartBlock;
class Statement;
class FlowchartList;
class FlowchartProgram;
class TuringMachineProgram;

using FlowchartValue = std::variant<
    FlowchartVariable,
    FlowchartLiteral,
    FlowchartLabel,
    Statement,
    TuringMachineProgram,
    FlowchartBlock,
    FlowchartProgram,
    FlowchartList,
    FlowchartProgramState
>;

void replaceAll(std::string &str, const std::string &from, const std::string &to) {
    size_t start_pos = 0;
    while ((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length();
    }
}

class FlowchartLabel {
public:
    string value;

    explicit FlowchartLabel(string val) : value(std::move(val)) {
        // if (!is_correct_string(value))
        //     throw runtime_error("Invalid label value");
    }

    FlowchartLabel() {
        value = "";
    }

    static bool is_correct_string(const string &s) {
        return s.size() >= 2 && s.front() == '#' && s.back() == '!';
    }

    bool operator<(const FlowchartLabel &other) const {
        return value < other.value;
    }

    bool operator==(const FlowchartLabel &other) const {
        return value == other.value;
    }
};

class FlowchartLiteral {
public:
    string value;

    explicit FlowchartLiteral(const string &val) : value(val.substr(1, val.size() - 2)) {
        if (!is_correct_string(val))
            throw runtime_error("Invalid literal value");
    }

    static bool is_correct_string(const string &s) {
        return s.size() >= 2 && s.front() == '%' && s.back() == '/';
    }

    bool operator<(const FlowchartLiteral &other) const {
        return value < other.value;
    }

    bool operator==(const FlowchartLiteral &other) const {
        return value == other.value;
    }

    [[nodiscard]] string to_string() const {
        return "%" + value + "/";
    }
};

class FlowchartVariable {
public:
    string name;

    explicit FlowchartVariable(string n): name(std::move(n)) {
        if (!is_correct_string(name))
            throw runtime_error("Invalid variable name");
    }

    static bool is_correct_string(const string &s) {
        return !s.empty() && regex_match(s, regex(R"(^[a-zA-Z_][a-zA-Z0-9_]*$)"));
    }

    bool operator<(const FlowchartVariable &other) const {
        return name < other.name;
    }

    bool operator==(const FlowchartVariable &other) const {
        return name == other.name;
    }
};

struct Util {
    static vector<char> open_parenthesis;
    static vector<char> closed_parenthesis;
    static map<string, int> functions;

    static vector<string> split_on_level(const string &s, const char symbol, const int level) {
        vector<string> result = {""};
        int balance = 0;

        for (char ch: s) {
            if (ranges::find(open_parenthesis, ch) != open_parenthesis.end()) {
                balance++;
                if (balance == level) continue;
            } else if (ranges::find(closed_parenthesis, ch) != closed_parenthesis.end()) {
                balance--;
                if (balance == level) {
                    result.back() += ch;
                    continue;
                }
            }

            if (balance < level) continue;
            if (balance > level) {
                result.back() += ch;
                continue;
            }

            if (ch == symbol && !result.back().empty()) {
                result.emplace_back("");
                continue;
            }
            if (ch != symbol)
                result.back() += ch;
        }
        if (result.back().empty()) result.pop_back();
        return result;
    }

    static bool is_correct_value(const string &s);

    static bool is_correct_several_expr(const vector<string> &tokens, const int expected_number) {
        if (expected_number == 0) return tokens.empty();
        int balance = expected_number;
        for (size_t i = 0; i < tokens.size(); ++i) {
            if (functions.contains(tokens[i])) {
                balance += functions[tokens[i]] - 1;
            } else if (is_correct_value(tokens[i])) {
                balance -= 1;
            } else {
                return false;
            }

            if (balance < 0 || (balance == 0 && i < tokens.size() - 1)) {
                return false;
            }
        }
        return balance == 0;
    }

    static bool is_correct_expr(const string &str) {
        const auto tokens = split_on_level(strip_spaces(str), ' ', 0);

        if (functions.contains(tokens[0])) {
            return is_correct_several_expr(vector(tokens.begin() + 1, tokens.end()), functions[tokens[0]]);
        }

        if (tokens.size() > 1) return false;

        return is_correct_value(tokens[0]);
    }

    static std::string join(const std::size_t begin, const std::size_t end, const std::vector<string> &v,
                            const string &separator) {
        if (end > v.size() || begin >= v.size() || begin >= end) return "";
        return std::accumulate(v.begin() + static_cast<long>(begin) + 1, v.begin() + static_cast<long>(end), v[begin],
                               [separator](std::string a, const std::string &b) {
                                   return std::move(a) + separator + b;
                               });
    }

    static bool is_correct_jump(const string &str) {
        const auto tokens = split_on_level(str, ' ', 0);
        if (tokens.size() == 2 && strip_spaces(tokens[0]) == "goto") {
            return FlowchartLabel::is_correct_string(tokens[1]);
        }
        if (tokens.size() >= 2 && strip_spaces(tokens[0]) == "return") {
            const std::string expr = join(1, tokens.size(), tokens, " ");
            return is_correct_expr(expr);
        }
        if (tokens.size() >= 6 && strip_spaces(tokens[0]) == "if" &&
            strip_spaces(tokens[tokens.size() - 4]) == "goto" &&
            strip_spaces(tokens[tokens.size() - 2]) == "else") {
            const std::string cond = join(1, tokens.size() - 4, tokens, " ");
            return is_correct_expr(cond) &&
                   FlowchartLabel::is_correct_string(tokens[tokens.size() - 3]) &&
                   FlowchartLabel::is_correct_string(tokens[tokens.size() - 1]);
        }
        return false;
    }

    static bool is_correct_assignment(const string &str) {
        const auto tokens = split_on_level(strip_spaces(str), ' ', 0);

        if (tokens.size() < 3 || strip_spaces(tokens[0]) != ":=") return false;

        const string expr = join(2, tokens.size(), tokens, " ");

        return FlowchartVariable::is_correct_string(tokens[1]) && is_correct_expr(expr);
    }

    static string strip(const string &str, const char c) {
        int start = 0;
        size_t end = str.size() - 1;
        while (str[start] == c) start++;
        while (str[end] == c) end--;
        return str.substr(start, end - start + 1);
    }

    static string strip_spaces(const string &str) {
        return strip(strip(strip(str, '\t'), '\n'), ' ');
    }
};

vector<char> Util::open_parenthesis = {'(', '[', '{', '<', '%', '#'};

vector<char> Util::closed_parenthesis = {')', ']', '}', '>', '/', '!'};

map<string, int> Util::functions = {
    {"hd", 1}, {"tl", 1}, {"firstInstruction", 1}, {"firstSym", 1}, {"firstCommand", 1}, {"rest", 1},
    {"lookupInitial", 1}, {"isEmpty", 1}, {"usedVars", 1},

    {"hasNext", 2}, {"==", 2}, {"cons", 2}, {"newTail", 2}, {"eval", 2}, {"reduce", 2},
    {"isStatic", 2}, {"consUnique", 2}, {"lookup", 2}, {"in", 2}, {"extendReturn", 2}, {"extendCode", 2},
    {"getLabel", 2}, {"parse", 2}, {"extendGoto", 2}, {"lookupLiteral", 2}, {"nextLabel", 2},

    {"addToState", 3}, {"extendAssignment", 3}, {"ternaryOperator", 3}, {"initialCode", 3},

    {"consUniqueIfNotInWithStateCompression", 4},

    {"extendIf", 6},
};

string value_to_string(optional<FlowchartValue> value);

template<typename T>
T *as(FlowchartValue &value);

template<typename T>
const T *const_as(const FlowchartValue &value);

optional<FlowchartLiteral> boolean_to_optional_value(const bool value) {
    return value ? optional(FlowchartLiteral("%true/")) : optional(FlowchartLiteral("%false/"));
}

class Statement {
public:
    std::vector<string> elems;
    bool split_by_spaces;
    bool split_by_expr;

    explicit Statement(const std::vector<string> &elems = {}, const std::string &code = "",
                       const bool split_by_spaces = false,
                       const bool split_by_expr = false): split_by_spaces(split_by_spaces),
                                                          split_by_expr(split_by_expr) {
        if (elems.empty()) {
            this->elems.clear();
            if (!code.empty()) {
                if (split_by_spaces) {
                    for (const auto &token: Util::split_on_level(Util::strip(code, ';'), ' ', 0)) {
                        this->elems.emplace_back(Util::strip_spaces(token));
                    }
                } else if (split_by_expr) {
                    vector<string> tokens;
                    for (const auto &token: Util::split_on_level(Util::strip(code, ';'), ' ', 0)) {
                        tokens.emplace_back(Util::strip_spaces(token));
                    }
                    if (tokens[0] == "if") {
                        const size_t index_of_goto = ranges::find(tokens, "goto") - tokens.begin();
                        this->elems.emplace_back(tokens[0]);
                        this->elems.emplace_back(Util::join(1, index_of_goto, tokens, " "));
                        this->elems.emplace_back(tokens[index_of_goto]);
                        this->elems.emplace_back(tokens[index_of_goto + 1]);
                        this->elems.emplace_back(tokens[index_of_goto + 2]);
                        this->elems.emplace_back(tokens[index_of_goto + 3]);
                    } else if (tokens[0] == "goto") {
                        this->elems.emplace_back(tokens[0]);
                        this->elems.emplace_back(tokens[1]);
                    } else if (tokens[0] == "return") {
                        this->elems.emplace_back(tokens[0]);
                        this->elems.emplace_back(Util::join(1, tokens.size(), tokens, " "));
                    } else if (tokens[0] == ":=") {
                        this->elems.emplace_back(tokens[0]);
                        this->elems.emplace_back(tokens[1]);
                        this->elems.emplace_back(Util::join(2, tokens.size(), tokens, " "));
                    }
                }
            } else {
                // throw std::runtime_error("Statement must be split either by spaces or expressions");
            }
        } else {
            this->elems = elems;
        }
    }

    [[nodiscard]] std::optional<FlowchartValue> head() const;

    [[nodiscard]] Statement tail() const {
        return elems.size() <= 1
                   ? Statement({}, "", split_by_spaces, split_by_expr)
                   : Statement(std::vector(elems.begin() + 1, elems.end()), "", split_by_spaces, split_by_expr);
    }

    void cons(const FlowchartLiteral &element) {
        elems.insert(elems.begin(), element.value);
    }

    [[nodiscard]] bool is_empty() const {
        return elems.empty();
    }

    bool operator==(const Statement &other) const {
        return elems == other.elems;
    }

    [[nodiscard]] std::string to_string() const {
        ostringstream oss;
        for (const auto &elem: elems) {
            oss << elem << " ";
        }
        return oss.str();
    }

    [[nodiscard]] string pretty_print() const {
        return to_string();
    }
};

class TuringMachineProgram {
public:
    map<FlowchartLabel, Statement> dictionary;
    std::vector<FlowchartLabel> order;

    TuringMachineProgram(const string &keys_values, const map<FlowchartLabel, Statement> &dictionary,
                         const std::vector<FlowchartLabel> &order) {
        this->dictionary = {};
        this->order = {};
        if (keys_values.empty()) {
            this->dictionary = dictionary;
            this->order = order;
        } else {
            if (keys_values != "<>") {
                for (const vector<string> keys_values_split = Util::split_on_level(
                         keys_values.substr(1, keys_values.size() - 2), '$',
                         0); const auto &key_value: keys_values_split) {
                    const auto tokens = Util::split_on_level(key_value, ':', 0);
                    const auto label = FlowchartLabel(Util::strip_spaces(tokens[0]));
                    this->dictionary[label] = Statement({}, Util::strip_spaces(tokens[1]), true, false);
                    this->order.emplace_back(label);
                }
            }
        }
    }

    static bool is_correct_string(const std::string &str) {
        return !str.empty() && str.front() == '<' && str.back() == '>';
    }

    [[nodiscard]] bool is_empty() const {
        return order.empty();
    }

    bool operator==(const TuringMachineProgram &other) const {
        return order == other.order && dictionary == other.dictionary;
    }

    [[nodiscard]] std::string to_string() const {
        std::ostringstream oss;
        oss << "<";
        for (size_t i = 0; i < order.size(); ++i) {
            if (i > 0) oss << " $ ";
            oss << order[i].value << ": " << dictionary.at(order[i]).to_string();
        }
        oss << ">";
        return oss.str();
    }

    [[nodiscard]] string pretty_print() const {
        return to_string();
    }
};

optional<FlowchartValue> value_from_raw(const string &raw, optional<FlowchartProgramState> state, bool is_reduce);

class FlowchartBlock {
public:
    std::vector<Statement> contents;
    FlowchartLabel label;

    explicit FlowchartBlock(FlowchartLabel label = FlowchartLabel(""), std::vector<Statement> contents = {})
        : contents(std::move(contents)), label(std::move(label)) {
    }

    void add_line(const Statement &line) {
        contents.emplace_back(line);
    }

    [[nodiscard]] optional<Statement> get_line(const size_t index) const {
        return index >= contents.size() ? nullopt : optional(contents[index]);
    }

    bool operator==(const FlowchartBlock &other) const {
        return label == other.label && contents == other.contents;
    }

    [[nodiscard]] size_t size() const {
        return contents.size();
    }

    [[nodiscard]] FlowchartBlock tail() const {
        return contents.size() < 2
                   ? FlowchartBlock(label, {})
                   : FlowchartBlock{label, std::vector(contents.begin() + 1, contents.end())};
    }

    [[nodiscard]] std::string to_string() const {
        std::ostringstream oss;
        oss << label.value << ": ";
        for (auto &line: contents) {
            oss << line.to_string() << "; ";
        }
        return oss.str();
    }


    [[nodiscard]] string pretty_print() const {
        std::ostringstream oss;
        oss << label.value << ":\n";
        for (auto &line: contents) {
            oss << "    " << line.to_string() << ";\n";
        }
        return oss.str();
    }
};

class FlowchartProgramState {
    map<FlowchartLabel, map<string, FlowchartLabel> > label_renaming;

    static FlowchartLabel next_label_name() {
        static int counter = 0;
        return FlowchartLabel("#lab" + std::to_string(counter++) + "!");
    }

public:
    map<FlowchartVariable, optional<FlowchartValue> > variables;

    FlowchartProgramState(const optional<FlowchartProgramState> &parent_state, bool is_reduce, const string &s);

    [[nodiscard]] bool is_empty() const;

    bool operator==(const FlowchartProgramState &other) const;

    static bool is_static(const FlowchartList &division, const string &expr);

    static bool is_correct_string(const string &s) {
        return !s.empty() && s.front() == '[' && s.back() == ']';
    }

    void append(const FlowchartVariable &name, const optional<FlowchartValue> &value);

    optional<FlowchartValue> evaluate(const string &expr);

    optional<FlowchartValue> reduce(const string &expr);

    [[nodiscard]] FlowchartProgramState compress(const FlowchartLabel &label, const FlowchartList &used_vars) const;

    static vector<string> split_to_expr(const vector<string> &tokens, int expr_number) {
        int balance = expr_number;
        vector<string> result;
        int last_index = 0;
        for (int i = 0; i < tokens.size(); i++) {
            if (const auto &token = tokens[i]; Util::functions.contains(token)) {
                balance += Util::functions[token] - 1;
            } else {
                balance--;
            }
            if (balance < expr_number) {
                result.emplace_back(Util::join(last_index, i + 1, tokens, " "));
                last_index = i + 1;
                expr_number--;
            }
            if (expr_number == 0) {
                return result;
            }
        }
        return result;
    }

    [[nodiscard]] string to_string() const;

    [[nodiscard]] string pretty_print() const {
        return to_string();
    }

    pair<bool, optional<FlowchartValue> > eval_expr(const string &expr, bool is_reduce);
};

class FlowchartList {
public:
    std::vector<optional<FlowchartValue> > values;

    FlowchartList(const std::optional<FlowchartProgramState> &state, bool isReduce, const std::string &s,
                  const optional<vector<optional<FlowchartValue> > > &values);

    FlowchartList(const std::string &s, const optional<vector<optional<FlowchartValue> > > &values);

    static bool is_correct_string(const std::string &str) {
        return !str.empty() && str.front() == '(' && str.back() == ')';
    }

    [[nodiscard]] optional<FlowchartValue> head() const;

    [[nodiscard]] FlowchartList tail() const;

    void cons(const optional<FlowchartValue> &elem);

    [[nodiscard]] bool is_empty() const;

    bool operator==(const FlowchartList &other) const;

    [[nodiscard]] std::string to_string() const;

    [[nodiscard]] string pretty_print() const {
        return to_string();
    }
};

class FlowchartProgram {
    map<FlowchartLabel, FlowchartBlock> blocks;
    bool is_reduce;
    optional<FlowchartProgramState> parent_state;
    int lookup_id = 0;
    string program;

public:
    vector<FlowchartLabel> labels;
    FlowchartProgramState state;
    map<FlowchartLabel, set<FlowchartVariable> > used_variables;

    FlowchartProgram(const optional<FlowchartProgramState> &parent_state, const bool is_reduce, const string &program,
                     const string &filename): state(parent_state, is_reduce, "") {
        this->labels = {};
        this->blocks = {};
        this->is_reduce = is_reduce;
        this->parent_state = parent_state;
        if (filename.empty()) {
            this->program = program;
        } else {
            ifstream ifs(filename);
            string input;
            while (std::getline(ifs, input)) {
                this->program += input;
            }
            ifs.close();
        }

        if (!is_correct_string(this->program))
            throw runtime_error("Invalid program provided");
    }

    void add_block(const FlowchartBlock &block) {
        labels.emplace_back(block.label);
        blocks[block.label] = block;
    }

    [[nodiscard]] FlowchartList get_used_vars() const {
        auto result = FlowchartList("()", {});
        auto lines = vector<string>{};
        for (const auto &raw_line: Util::split_on_level(Util::strip_spaces(program.substr(1, program.size() - 2)), ';',
                                                        0)) {
            auto line = Util::strip_spaces(raw_line);
            if (line.empty()) continue;
            lines.emplace_back(line);
        }

        int i = 0;
        if (lines[0].rfind("read") == 0) {
            i++;
        }

        while (i < lines.size()) {
            const auto raw_tokens = Util::split_on_level(lines[i], ':', 0);
            vector<string> tokens;
            tokens.reserve(raw_tokens.size());
            for (const auto &token: raw_tokens) {
                tokens.emplace_back(Util::strip_spaces(token));
            }
            auto label = FlowchartLabel(Util::strip_spaces(tokens[0]));
            string line = Util::join(1, tokens.size(), tokens, ":");

            result.values.emplace_back(FlowchartList("", vector{
                                                         optional<FlowchartValue>(label),
                                                         optional<FlowchartValue>(FlowchartList("()", {}))
                                                     }));
            set<FlowchartVariable> rewrote = {};
            while (!Util::is_correct_jump(line)) {
                auto cmd_tokens = Util::split_on_level(line, ' ', 0);
                for (int o = 2; o < cmd_tokens.size(); o++) {
                    if (Util::functions.contains(cmd_tokens[o])) continue;
                    if (!FlowchartVariable::is_correct_string(cmd_tokens[o])) continue;
                    if (rewrote.contains(FlowchartVariable(cmd_tokens[o]))) continue;
                    as<FlowchartList>(
                                as<FlowchartList>(result.values[result.values.size() - 1].value())->values[1].value())->
                            values.emplace_back(FlowchartLiteral("%" + cmd_tokens[o] + "/"));
                }
                rewrote.insert(FlowchartVariable(cmd_tokens[1]));

                i++;
                line = lines[i];
            }
            auto cmd_tokens = Util::split_on_level(line, ' ', 0);
            if (cmd_tokens[0] == "return") {
                for (int o = 1; o < cmd_tokens.size(); o++) {
                    if (Util::functions.contains(cmd_tokens[o])) continue;
                    if (!FlowchartVariable::is_correct_string(cmd_tokens[o])) continue;
                    if (rewrote.contains(FlowchartVariable(cmd_tokens[o]))) continue;
                    as<FlowchartList>(
                                as<FlowchartList>(result.values[result.values.size() - 1].value())->values[1].value())->
                            values.emplace_back(FlowchartLiteral("%" + cmd_tokens[o] + "/"));
                }
            } else if (cmd_tokens[0] == "if") {
                for (int o = 1; o < cmd_tokens.size() - 4; o++) {
                    if (Util::functions.contains(cmd_tokens[o])) continue;
                    if (!FlowchartVariable::is_correct_string(cmd_tokens[o])) continue;
                    if (rewrote.contains(FlowchartVariable(cmd_tokens[o]))) continue;
                    as<FlowchartList>(
                                as<FlowchartList>(result.values[result.values.size() - 1].value())->values[1].value())->
                            values.emplace_back(FlowchartLiteral("%" + cmd_tokens[o] + "/"));
                }
            }
            i++;
        }
        return result;
    }

    static bool is_correct_string(const string &s) {
        if (s == "{}") return true;
        if (s[0] != '{' || s[s.size() - 1] != '}') {
            return false;
        }
        const string str = Util::strip_spaces(s.substr(1, s.size() - 2));
        auto lines = vector<string>{};
        for (const auto &raw_line: Util::split_on_level(Util::strip_spaces(str), ';', 0)) {
            auto line = Util::strip_spaces(raw_line);
            if (line.empty()) continue;
            lines.emplace_back(line);
        }
        int i = 0;
        if (lines[0].rfind("read") == 0) {
            for (const auto tokens = Util::split_on_level(lines[0].substr(4), ',', 0); const auto &token: tokens) {
                if (!FlowchartVariable::is_correct_string(Util::strip_spaces(token))) {
                    return false;
                }
            }
            i++;
        }
        while (i < lines.size()) {
            const auto raw_tokens = Util::split_on_level(lines[i], ':', 0);
            vector<string> tokens;
            tokens.reserve(raw_tokens.size());
            for (const auto &token: raw_tokens) {
                tokens.emplace_back(Util::strip_spaces(token));
            }
            string label = Util::strip_spaces(tokens[0]);
            string line = Util::join(1, tokens.size(), tokens, ":");

            if (!FlowchartLabel::is_correct_string(label)) {
                return false;
            }

            while (!Util::is_correct_jump(line)) {
                if (!Util::is_correct_assignment(line)) {
                    Util::is_correct_jump(line);
                    return false;
                }
                i++;
                line = lines[i];
            }
            i++;
        }
        return true;
    }

    FlowchartProgram parse_program(const bool read_from_input, const optional<FlowchartProgramState> &state,
                                   ifstream &ifs) const {
        auto lines = vector<string>{};
        for (const auto &raw_line: Util::split_on_level(Util::strip_spaces(program.substr(1, program.size() - 2)), ';',
                                                        0)) {
            auto line = Util::strip_spaces(raw_line);
            if (line.empty()) continue;
            lines.emplace_back(line);
        }
        auto result = FlowchartProgram(parent_state, is_reduce, program, "");
        int i = 0;
        if (lines[0].rfind("read") == 0) {
            for (const auto tokens = Util::split_on_level(lines[0].substr(4), ',', 0); const auto &token: tokens) {
                auto key = FlowchartVariable(Util::strip_spaces(token));
                if (read_from_input) {
                    std::string input;
                    getline(ifs, input);
                    result.state.variables[key] = value_from_raw(input, nullopt, false);
                } else {
                    if (state.has_value() && state.value().variables.contains(key)) {
                        result.state.variables[key] = state.value().variables.at(key);
                    } else {
                        result.state.variables[key] = nullopt;
                    }
                }
            }
            i++;
        }

        while (i < lines.size()) {
            const auto raw_tokens = Util::split_on_level(lines[i], ':', 0);
            vector<string> tokens;
            tokens.reserve(raw_tokens.size());
            for (const auto &token: raw_tokens) {
                tokens.emplace_back(Util::strip_spaces(token));
            }
            auto label = FlowchartLabel(Util::strip_spaces(tokens[0]));
            string line = Util::join(1, tokens.size(), tokens, ":");

            result.labels.emplace_back(label);
            result.blocks[label] = FlowchartBlock(label, {});
            result.used_variables[label] = {};
            set<FlowchartVariable> rewrote = {};
            while (!Util::is_correct_jump(line)) {
                if (line.rfind(" parse ") != string::npos) {
                    auto args = Util::split_on_level(Util::strip_spaces(line), ' ', 0);
                    const auto &parsed_program_arg = FlowchartVariable(args[1]);
                    auto program_arg = as<FlowchartProgram>(result.state.variables[FlowchartVariable(args[3])].value());
                    const auto &vs_arg = FlowchartVariable(args[4]);
                    if (result.state.variables.contains(vs_arg)) {
                        if (!result.state.variables[vs_arg].has_value())
                            result.state.variables[parsed_program_arg] = program_arg->
                                    parse_program(false, nullopt, ifs);
                        else
                            result.state.variables[parsed_program_arg] = program_arg->parse_program(
                                false, *as<FlowchartProgramState>(result.state.variables[vs_arg].value()), ifs);
                    } else
                        result.state.variables[parsed_program_arg] = program_arg->parse_program(false, nullopt, ifs);
                    if (result.state.variables.contains(vs_arg) && result.state.variables[vs_arg].has_value() && as<
                            FlowchartProgramState>(result.state.variables[vs_arg].value())->variables.contains(
                            parsed_program_arg))
                        as<FlowchartProgramState>(result.state.variables[vs_arg].value())->variables[parsed_program_arg]
                                = as<FlowchartProgram>(result.state.variables[parsed_program_arg].value())->state.
                                variables[parsed_program_arg];
                } else {
                    result.blocks[label].add_line(Statement({}, line, false, true));
                }

                auto cmd_tokens = Util::split_on_level(line, ' ', 0);
                for (int o = 2; o < cmd_tokens.size(); o++) {
                    if (Util::functions.contains(cmd_tokens[o])) continue;
                    if (!FlowchartVariable::is_correct_string(cmd_tokens[o])) continue;
                    if (rewrote.contains(FlowchartVariable(cmd_tokens[o]))) continue;
                    result.used_variables[label].insert(FlowchartVariable(cmd_tokens[o]));
                }
                rewrote.insert(FlowchartVariable(cmd_tokens[1]));

                i++;
                line = lines[i];
            }
            auto cmd_tokens = Util::split_on_level(line, ' ', 0);
            if (cmd_tokens[0] == "return") {
                for (int o = 1; o < cmd_tokens.size(); o++) {
                    if (Util::functions.contains(cmd_tokens[o])) continue;
                    if (!FlowchartVariable::is_correct_string(cmd_tokens[o])) continue;
                    if (rewrote.contains(FlowchartVariable(cmd_tokens[o]))) continue;
                    result.used_variables[label].insert(FlowchartVariable(cmd_tokens[o]));
                }
            } else if (cmd_tokens[0] == "if") {
                for (int o = 1; o < cmd_tokens.size() - 4; o++) {
                    if (Util::functions.contains(cmd_tokens[o])) continue;
                    if (!FlowchartVariable::is_correct_string(cmd_tokens[o])) continue;
                    if (rewrote.contains(FlowchartVariable(cmd_tokens[o]))) continue;
                    result.used_variables[label].insert(FlowchartVariable(cmd_tokens[o]));
                }
            }
            result.blocks[label].add_line(Statement({}, line, false, true));
            i++;
        }
        return result;
    }

    FlowchartBlock get_block(const FlowchartLabel &label) {
        return blocks[label];
    }

    bool has_next(const FlowchartLabel &label) {
        return ranges::find(labels, label) != labels.end();
    }

    FlowchartLabel get_label(const int index) {
        return labels[index];
    }

    FlowchartLabel next_label(const FlowchartLabel &label) {
        const auto index = ranges::find(labels, label) - labels.begin() + 1;
        return index < labels.size() ? labels[index] : FlowchartLabel("#fail!");
    }

    [[nodiscard]] std::string to_string() const {
        std::ostringstream oss;
        oss << "{";
        for (const auto &label: labels) {
            oss << blocks.at(label).to_string() << " ";
        }
        oss << "}";
        return oss.str();
    }

    [[nodiscard]] std::string pretty_print() const {
        std::ostringstream oss;
        oss << "{\n";
        for (const auto &label: labels) {
            oss << blocks.at(label).pretty_print() << "\n\n";
        }
        oss << "}";
        return oss.str();
    }
};

template<typename T>
T *as(FlowchartValue &value) {
    return get_if<T>(&value);
}

template<typename T>
const T *const_as(const FlowchartValue &value) {
    return std::get_if<T>(&value);
}

string value_to_string(optional<FlowchartValue> value) {
    if (value.has_value()) {
        if (const auto *stmt = as<Statement>(value.value())) {
            return stmt->to_string();
        }
        if (const auto *block = as<FlowchartBlock>(value.value())) {
            return block->to_string();
        }
        if (const auto *program = as<FlowchartProgram>(value.value())) {
            return program->to_string();
        }
        if (const auto *state = as<FlowchartProgramState>(value.value())) {
            return state->to_string();
        }
        if (const auto *list = as<FlowchartList>(value.value())) {
            return list->to_string();
        }
        if (const auto *tm_program = as<TuringMachineProgram>(value.value())) {
            return tm_program->to_string();
        }
        if (const auto *label = as<FlowchartLabel>(value.value())) {
            return label->value;
        }
        if (const auto *var = as<FlowchartVariable>(value.value())) {
            return var->name;
        }
        if (const auto *literal = as<FlowchartLiteral>(value.value())) {
            return literal->to_string();
        }
        throw std::runtime_error("Unexpected value");
    }
    return "None";
}

string pretty_print_value(optional<FlowchartValue> value) {
    if (value.has_value()) {
        if (const auto *stmt = as<Statement>(value.value())) {
            return stmt->pretty_print();
        }
        if (const auto *block = as<FlowchartBlock>(value.value())) {
            return block->pretty_print();
        }
        if (const auto *program = as<FlowchartProgram>(value.value())) {
            return program->pretty_print();
        }
        if (const auto *state = as<FlowchartProgramState>(value.value())) {
            return state->pretty_print();
        }
        if (const auto *list = as<FlowchartList>(value.value())) {
            return list->pretty_print();
        }
        if (const auto *tm_program = as<TuringMachineProgram>(value.value())) {
            return tm_program->pretty_print();
        }
        if (const auto *label = as<FlowchartLabel>(value.value())) {
            return label->value;
        }
        if (const auto *var = as<FlowchartVariable>(value.value())) {
            return var->name;
        }
        if (const auto *literal = as<FlowchartLiteral>(value.value())) {
            return literal->to_string();
        }
        throw std::runtime_error("Unexpected value");
    }
    return "None";
}

bool FlowchartProgramState::is_static(const FlowchartList &division, const string &expr) {
    auto tokens = Util::split_on_level(expr, ' ', 0);
    if (tokens.size() == 1) {
        bool found = false;
        for (const auto &v: division.values) {
            if (const_as<FlowchartVariable>(v.value())->name == tokens[0]) {
                found = true;
                break;
            }
        }
        if (found) {
            return true;
        }
        if (Util::is_correct_value(tokens[0]) && !FlowchartVariable::is_correct_string(tokens[0])) {
            return true;
        }
        return false;
    }

    return ranges::all_of(split_to_expr(vector(tokens.begin() + 1, tokens.end()), Util::functions[tokens[0]]),
                          [&](const string &s) { return is_static(division, s); });
}

optional<FlowchartValue>
value_from_raw(const string &raw, optional<FlowchartProgramState> state, const bool is_reduce) {
    const string s = Util::strip_spaces(raw);
    if (FlowchartList::is_correct_string(s)) return FlowchartList(state, is_reduce, s, {});
    if (TuringMachineProgram::is_correct_string(s)) return TuringMachineProgram(s, {}, {});
    if (FlowchartProgramState::is_correct_string(s)) return FlowchartProgramState(state, is_reduce, s);
    if (FlowchartProgram::is_correct_string(s)) return FlowchartProgram(state, is_reduce, s, "");
    if (FlowchartLiteral::is_correct_string(s)) return FlowchartLiteral(s);
    if (FlowchartVariable::is_correct_string(s))
        return state.has_value()
                   ? state.value().eval_expr(s, is_reduce).second
                   : FlowchartVariable(s);
    if (FlowchartLabel::is_correct_string(s)) return FlowchartLabel(s);
    throw std::runtime_error("FlowchartValue is not a FlowchartValue");
}

class FlowchartInterpreter {
    FlowchartProgram program;

    optional<FlowchartLabel> execute_block(const FlowchartLabel &label) {
        const auto block = program.get_block(label);
        size_t i = 0;

        while (i < block.size()) {
            string stmt = block.get_line(i)->to_string();
            if (auto tokens = Util::split_on_level(stmt, ' ', 0); tokens[0] == ":=") {
                std::string expr = Util::join(2, tokens.size(), tokens, " ");
                program.state.variables[FlowchartVariable(tokens[1])] = program.state.eval_expr(expr, false).second;
            } else if (tokens[0] == "goto") {
                return FlowchartLabel(tokens[1]);
            } else if (tokens[0] == "if") {
                const auto result = program.state.eval_expr(Util::join(1, tokens.size() - 4, tokens, " "), false).
                        second;
                return const_as<FlowchartLiteral>(result.value())->value == "true"
                           ? FlowchartLabel(tokens[tokens.size() - 3])
                           : FlowchartLabel(tokens[tokens.size() - 1]);
            } else if (tokens[0] == "return") {
                const auto result = program.state.eval_expr(Util::join(1, tokens.size(), tokens, " "), false).second;
                cout << "Returned:" << endl << pretty_print_value(result) << endl;
                return nullopt;
            } else {
                throw std::runtime_error("Unexpected statement");
            }
            i++;
        }
        return nullopt;
    }

    void run() {
        std::optional current_label = program.get_label(0);
        while (current_label.has_value()) {
            current_label = execute_block(current_label.value());
        }
    }

    FlowchartInterpreter(const std::string &program_data, const std::string &filename, ifstream &ifs)
        : program(nullopt, false, program_data, filename) {
        program = program.parse_program(true, nullopt, ifs);
    }

public:
    static void run_from_file(const std::string &filename, ifstream &ifs) {
        FlowchartInterpreter interpreter("", filename, ifs);
        interpreter.run();
    }

    static void run_from_program(const std::string &program, ifstream &ifs) {
        FlowchartInterpreter interpreter(program, "", ifs);
        interpreter.run();
    }
};

FlowchartProgramState::FlowchartProgramState(const optional<FlowchartProgramState> &parent_state, const bool is_reduce,
                                             const string &s) {
    this->variables = {};
    if (!s.empty() && s != "[]") {
        const auto tmp = Util::split_on_level(s.substr(1, s.size() - 2), '$', 0);
        for (int i = 0; i < tmp.size(); i += 2) {
            variables[FlowchartVariable(Util::strip_spaces(tmp[i]))] = value_from_raw(
                Util::strip_spaces(tmp[i + 1]), parent_state, is_reduce);
        }
    }
}

bool FlowchartProgramState::is_empty() const {
    return variables.empty();
}


bool equal_values(const optional<FlowchartValue> &a, const optional<FlowchartValue> &b) {
    bool result;
    if (a.has_value() != b.has_value()) result = false;
    else if (!a.has_value()) result = true;
    else if (auto *stmt1 = const_as<Statement>(a.value())) {
        if (auto *stmt2 = const_as<Statement>(b.value())) {
            result = *stmt1 == *stmt2;
        } else result = false;
    } else if (auto *tm_program1 = const_as<TuringMachineProgram>(a.value())) {
        if (auto *tm_program2 = const_as<TuringMachineProgram>(b.value())) {
            result = *tm_program1 == *tm_program2;
        } else result = false;
    } else if (auto *block1 = const_as<FlowchartBlock>(a.value())) {
        if (auto *block2 = const_as<FlowchartBlock>(b.value())) {
            result = *block1 == *block2;
        } else result = false;
    } else if (auto *state1 = const_as<FlowchartProgramState>(a.value())) {
        if (auto *state2 = const_as<FlowchartProgramState>(b.value())) {
            result = *state1 == *state2;
        } else result = false;
    } else if (auto *program1 = const_as<FlowchartProgram>(a.value())) {
        if (auto *program2 = const_as<FlowchartProgram>(b.value())) {
            result = program1->to_string() == program2->to_string();
        } else result = false;
    } else if (auto *list1 = const_as<FlowchartList>(a.value())) {
        if (auto *list2 = const_as<FlowchartList>(b.value())) {
            result = *list1 == *list2;
        } else result = false;
    } else if (auto *label1 = const_as<FlowchartLabel>(a.value())) {
        if (auto *label2 = const_as<FlowchartLabel>(b.value())) {
            result = *label1 == *label2;
        } else result = false;
    } else if (auto *var1 = const_as<FlowchartVariable>(a.value())) {
        if (auto *var2 = const_as<FlowchartVariable>(b.value())) {
            result = *var1 == *var2;
        } else result = false;
    } else if (auto *literal1 = const_as<FlowchartLiteral>(a.value())) {
        if (auto *literal2 = const_as<FlowchartLiteral>(b.value())) {
            result = *literal1 == *literal2;
        } else result = false;
    } else {
        throw runtime_error("FlowchartList::equal_values() failed");
    }
    return result;
}

bool FlowchartProgramState::operator==(const FlowchartProgramState &other) const {
    if (variables.size() != other.variables.size()) return false;
    for (const auto &[key, value]: variables) {
        if (!other.variables.contains(key)) return false;
        if (value.has_value() != other.variables.at(key).has_value()) return false;
        if (!value.has_value()) continue;

        if (!equal_values(value, other.variables.at(key))) return false;
    }
    return true;
}

void FlowchartProgramState::append(const FlowchartVariable &name, const optional<FlowchartValue> &value) {
    variables[name] = value;
}

optional<FlowchartValue> FlowchartProgramState::evaluate(const string &expr) {
    return eval_expr(expr, false).second;
}

optional<FlowchartValue> FlowchartProgramState::reduce(const string &expr) {
    return eval_expr(expr, true).second;
}

FlowchartList::FlowchartList(const std::optional<FlowchartProgramState> &state, bool isReduce, const std::string &s,
                             const optional<vector<optional<FlowchartValue> > > &values) {
    if (values.has_value()) {
        this->values = values.value();
    } else if (s == "()" || s.empty()) {
        this->values = {};
    } else {
        const auto tokens = Util::split_on_level(s.substr(1, s.size() - 2), '$', 0);
        for (int i = 0; i < tokens.size(); i++) {
            this->values.emplace_back(value_from_raw(tokens[tokens.size() - 1 - i], state, isReduce));
        }
    }
}

FlowchartList::FlowchartList(const std::string &s,
                             const optional<std::vector<optional<FlowchartValue> > > &values) {
    if (values.has_value()) {
        this->values = values.value();
    } else if (s == "()" || s.empty()) {
        this->values = {};
    }
}

[[nodiscard]] optional<FlowchartValue> FlowchartList::head() const {
    return values.empty() ? nullopt : optional(values.back());
}

[[nodiscard]] FlowchartList FlowchartList::tail() const {
    return values.size() < 2
               ? FlowchartList("", optional(vector<optional<FlowchartValue> >{}))
               : FlowchartList("", vector(values.begin(), values.end() - 1));
}

void FlowchartList::cons(const optional<FlowchartValue> &elem) {
    values.emplace_back(elem);
}

bool FlowchartList::is_empty() const {
    return values.empty();
}

bool FlowchartList::operator==(const FlowchartList &other) const {
    if (values.size() != other.values.size()) return false;
    for (int i = 0; i < values.size(); i++) {
        if (values[i].has_value() != other.values[i].has_value()) return false;
        if (!values[i].has_value()) continue;

        if (!equal_values(values[i], other.values[i])) return false;
    }
    return true;
}

FlowchartProgramState
FlowchartProgramState::compress(const FlowchartLabel &label, const FlowchartList &used_vars) const {
    auto result = FlowchartProgramState(nullopt, false, "");
    for (auto val: used_vars.values) {
        if (auto *l = as<FlowchartList>(val.value())) {
            if (*as<FlowchartLabel>(l->values[0].value()) == label) {
                for (const auto &v: as<FlowchartList>(l->values[1].value())->values) {
                    auto var = *const_as<FlowchartLiteral>(v.value());
                    if (!variables.contains(FlowchartVariable(var.value)))
                        result.append(
                            FlowchartVariable(var.value), nullopt);
                    else result.append(FlowchartVariable(var.value), variables.at(FlowchartVariable(var.value)));
                }
                return result;
            }
        }
    }
    throw runtime_error("FlowchartProgramState::compress failed");
}

std::optional<FlowchartValue> Statement::head() const {
    if (elems.empty()) return nullopt;
    if (FlowchartLiteral::is_correct_string(elems[0])) return FlowchartLiteral(elems[0]);
    return FlowchartLiteral('%' + elems[0] + '/');
}

string string_from_literal_or_value(optional<FlowchartValue> raw) {
    if (auto *literal = as<FlowchartLiteral>(raw.value())) {
        return literal->value;
    }
    return value_to_string(raw.value());
}

bool equal_label_state(const FlowchartList &a, const FlowchartList &b, const FlowchartList &used_vars) {
    auto a_label = FlowchartLabel(string_from_literal_or_value(a.values[1].value()));
    auto b_label = FlowchartLabel(string_from_literal_or_value(b.values[1].value()));

    if (a_label != b_label) return false;

    auto a_state = const_as<FlowchartProgramState>(a.values[0].value())->compress(a_label, used_vars);
    auto b_state = const_as<FlowchartProgramState>(b.values[0].value())->compress(b_label, used_vars);

    return a_state == b_state;
}

[[nodiscard]] std::string FlowchartList::to_string() const {
    std::ostringstream oss;
    oss << "(";
    for (size_t i = 0; i < values.size(); ++i) {
        if (i > 0) oss << " $ ";
        oss << value_to_string(values[values.size() - 1 - i]);
    }
    oss << ")";
    return oss.str();
}

pair<bool, optional<FlowchartValue> >
FlowchartProgramState::eval_expr(const string &expr, bool is_reduce) {
    auto tokens = Util::split_on_level(expr, ' ', 0);
    if (tokens.size() == 1) {
        if (FlowchartVariable::is_correct_string(tokens[0]) && variables.contains(FlowchartVariable(tokens[0]))) {
            return make_pair(true, variables.at(FlowchartVariable(tokens[0])));
        }
        if (Util::is_correct_value(tokens[0]) && !FlowchartVariable::is_correct_string(tokens[0])) {
            return make_pair(true, value_from_raw(tokens[0], *this, is_reduce));
        }
        if (is_reduce && FlowchartVariable::is_correct_string(tokens[0])) {
            return make_pair(false, FlowchartVariable(expr));
        }
    }

    if (string op = tokens[0]; Util::functions.contains(op)) {
        const auto args = split_to_expr(vector(tokens.begin() + 1, tokens.end()), Util::functions[op]);
        vector<optional<FlowchartValue> > values = {};
        bool success = true;
        string reduced, additional_code;
        for (const auto &arg: args) {
            reduced += " ";
            auto [r, v] = eval_expr(arg, is_reduce);
            success = success && r;
            values.push_back(v);

            if (!r) {
                if (auto *var = const_as<FlowchartVariable>(v.value())) {
                    reduced += var->name;
                } else {
                    reduced += const_as<FlowchartLiteral>(v.value())->value;
                }
            } else {
                reduced += value_to_string(v);
            }
        }
        if (!success) {
            return make_pair(false, optional(FlowchartLiteral('%' + op + reduced + '/')));
        }
        if (op == "hd") {
            if (!values[0].has_value()) {
                return make_pair(true, nullopt);
            }

            if (auto *stmt = as<Statement>(values[0].value())) {
                return make_pair(true, optional(stmt->head()));
            }
            if (auto *list = as<FlowchartList>(values[0].value())) {
                return make_pair(true, list->head());
            }
        } else if (op == "tl") {
            if (!values[0].has_value()) {
                return make_pair(true, nullopt);
            }

            if (auto *stmt = as<Statement>(values[0].value())) {
                return make_pair(true, optional(stmt->tail()));
            }
            if (auto *list = as<FlowchartList>(values[0].value())) {
                return make_pair(true, optional(list->tail()));
            }
            if (auto *block = as<FlowchartBlock>(values[0].value())) {
                return make_pair(true, optional(block->tail()));
            }
        } else if (op == "cons") {
            if (!values[0].has_value()) {
                return make_pair(true, nullopt);
            }

            if (auto *stmt = as<Statement>(values[1].value())) {
                stmt->cons(*as<FlowchartLiteral>(values[0].value()));
                return make_pair(true, optional(*stmt));
            }
            if (auto *list = as<FlowchartList>(values[1].value())) {
                list->cons(values[0].value());
                return make_pair(true, optional(*list));
            }
        } else if (op == "==") {
            return make_pair(true, boolean_to_optional_value(equal_values(values[0], values[1])));
        } else if (op == "newTail") {
            if (!values[0].has_value() || !values[1].has_value()) {
                return make_pair(true, nullopt);
            }

            auto *tm_program = as<TuringMachineProgram>(values[1].value());
            auto dictionary = tm_program->dictionary;
            auto order = tm_program->order;
            auto label = *as<FlowchartLiteral>(values[0].value());
            int index = 0;
            for (; index < order.size(); index++) {
                if (order[index].value == label.value) break;
            }
            auto new_order = vector(order.begin() + index, order.end());
            map<FlowchartLabel, Statement> new_dictionary = {};
            for (const auto &k: new_order) {
                new_dictionary[k] = dictionary[k];
            }
            return make_pair(true, optional(TuringMachineProgram("", new_dictionary, new_order)));
        } else if (op == "firstInstruction") {
            if (!values[0].has_value()) {
                return make_pair(true, nullopt);
            }

            auto *tm_program = as<TuringMachineProgram>(values[0].value());
            auto dictionary = tm_program->dictionary;
            auto order = tm_program->order;
            return make_pair(true, optional(dictionary[order[0]]));
        } else if (op == "firstSym") {
            if (!values[0].has_value()) {
                return make_pair(true, optional(FlowchartLiteral("%/")));
            }

            auto *list = as<FlowchartList>(values[0].value());
            return make_pair(true, list->head());
        } else if (op == "firstCommand") {
            if (!values[0].has_value()) {
                return make_pair(true, nullopt);
            }

            auto *block = as<FlowchartBlock>(values[0].value());
            return make_pair(true, block->get_line(0));
        } else if (op == "rest") {
            if (!values[0].has_value()) {
                return make_pair(true, nullopt);
            }

            auto *tm_program = as<TuringMachineProgram>(values[0].value());
            auto dictionary = tm_program->dictionary;
            auto order = tm_program->order;
            auto new_order = vector(order.begin() + 1, order.end());
            map<FlowchartLabel, Statement> new_dictionary = {};
            for (const auto &k: new_order) {
                new_dictionary[k] = dictionary[k];
            }
            return make_pair(true, optional(TuringMachineProgram("", new_dictionary, new_order)));
        } else if (op == "initialCode") {
            auto label = FlowchartLabel(string_from_literal_or_value(values[0]));
            auto state_str = value_to_string(
                const_as<FlowchartProgramState>(values[1].value())->compress(
                    label, *const_as<FlowchartList>(values[2].value())));
            FlowchartLabel renamed_label = (label_renaming.contains(label) && label_renaming[label].contains(state_str))
                                               ? label_renaming[label][state_str]
                                               : next_label_name();
            label_renaming[label][state_str] = renamed_label;
            return make_pair(true, FlowchartBlock(renamed_label));
        } else if (op == "extendIf") {
            auto true_label = FlowchartLabel(string_from_literal_or_value(values[2])),
                    false_label = FlowchartLabel(string_from_literal_or_value(values[3]));
            string compressed_true_state = value_to_string(
                        const_as<FlowchartProgramState>(values[4].value())->compress(
                            true_label, *const_as<FlowchartList>(values[5].value()))),
                    compressed_false_state = value_to_string(
                        const_as<FlowchartProgramState>(values[4].value())->compress(
                            false_label, *const_as<FlowchartList>(values[5].value())));

            FlowchartLabel renamed_true_label = label_renaming.contains(true_label) && label_renaming[true_label].
                                                contains(compressed_true_state)
                                                    ? label_renaming[true_label][compressed_true_state]
                                                    : next_label_name();
            label_renaming[true_label][compressed_true_state] = renamed_true_label;
            FlowchartLabel renamed_false_label = label_renaming.contains(false_label) && label_renaming[false_label].
                                                 contains(compressed_false_state)
                                                     ? label_renaming[false_label][compressed_false_state]
                                                     : next_label_name();
            label_renaming[false_label][compressed_false_state] = renamed_false_label;

            auto updated = *as<FlowchartBlock>(values[0].value());
            updated.add_line(Statement(
                {}, "if " + string_from_literal_or_value(values[1]) + " goto " + renamed_true_label.value + " else " +
                    renamed_false_label.value, false, true));
            return make_pair(true, updated);
        } else if (op == "extendReturn") {
            auto updated = *as<FlowchartBlock>(values[0].value());
            updated.add_line(Statement({}, "return " + string_from_literal_or_value(values[1]), false, true));
            return make_pair(true, updated);
        } else if (op == "extendAssignment") {
            auto updated = *as<FlowchartBlock>(values[0].value());
            updated.add_line(Statement(
                {}, ":= " + string_from_literal_or_value(values[1]) + " " + string_from_literal_or_value(values[2]),
                false, true));
            return make_pair(true, updated);
        } else if (op == "extendCode") {
            as<FlowchartProgram>(values[0].value())->add_block(*const_as<FlowchartBlock>(values[1].value()));
            return make_pair(true, *as<FlowchartProgram>(values[0].value()));
        } else if (op == "eval") {
            auto *program_state = as<FlowchartProgramState>(values[1].value());
            return make_pair(true, program_state->evaluate(as<FlowchartLiteral>(values[0].value())->value));
        } else if (op == "reduce") {
            auto *program_state = as<FlowchartProgramState>(values[1].value());
            return make_pair(true, program_state->reduce(as<FlowchartLiteral>(values[0].value())->value));
        } else if (op == "addToState") {
            auto *program_state = as<FlowchartProgramState>(values[0].value());
            auto var = FlowchartVariable(as<FlowchartLiteral>(values[1].value())->value);
            program_state->append(var, values[2]);
            return make_pair(true, optional(*program_state));
        } else if (op == "isStatic") {
            return make_pair(true, boolean_to_optional_value(
                                 is_static(*as<FlowchartList>(values[0].value()),
                                           as<FlowchartLiteral>(values[1].value())->value)));
        } else if (op == "lookup") {
            auto *program = as<FlowchartProgram>(values[1].value());
            auto label = FlowchartLabel(string_from_literal_or_value(values[0]));
            return make_pair(true, optional(program->get_block(label)));
        } else if (op == "in") {
            for (auto *list = as<FlowchartList>(values[1].value()); optional<FlowchartValue> &v: list->values) {
                if (equal_values(v, values[0])) {
                    return make_pair(true, boolean_to_optional_value(true));
                }
            }
            return make_pair(true, boolean_to_optional_value(false));
        } else if (op == "lookupInitial") {
            auto *program = as<FlowchartProgram>(values[0].value());
            return make_pair(true, optional(program->labels[0]));
        } else if (op == "isEmpty") {
            if (!values[0].has_value()) {
                return make_pair(true, boolean_to_optional_value(true));
            }
            if (auto *tm_program = as<TuringMachineProgram>(values[0].value())) {
                return make_pair(true, boolean_to_optional_value(tm_program->is_empty()));
            }
            if (auto *block = as<FlowchartBlock>(values[0].value())) {
                return make_pair(true, boolean_to_optional_value(block->size() == 0));
            }
            if (auto *list = as<FlowchartList>(values[0].value())) {
                return make_pair(true, boolean_to_optional_value(list->is_empty()));
            }
            if (auto *state = as<FlowchartProgramState>(values[0].value())) {
                return make_pair(true, boolean_to_optional_value(state->is_empty()));
            }
        } else if (op == "nextLabel") {
            auto *program = as<FlowchartProgram>(values[1].value());
            return make_pair(true, program->next_label(*as<FlowchartLabel>(values[0].value())));
        } else if (op == "getLabel") {
            auto *program = as<FlowchartProgram>(values[1].value());
            return make_pair(true, program->get_label(stoi(as<FlowchartLiteral>(values[0].value())->value)));
        } else if (op == "hasNext") {
            auto *program = as<FlowchartProgram>(values[1].value());
            return make_pair(
                true, boolean_to_optional_value(program->has_next(*as<FlowchartLabel>(values[0].value()))));
        } else if (op == "consUniqueIfNotInWithStateCompression") {
            if (values[1].has_value()) {
                auto *list = as<FlowchartList>(values[1].value());
                for (auto &v: list->values) {
                    if (equal_label_state(*const_as<FlowchartList>(v.value()),
                                          *const_as<FlowchartList>(values[0].value()),
                                          *const_as<FlowchartList>(values[3].value()))) {
                        return make_pair(true, values[1]);
                    }
                }
            }
            if (values[2].has_value()) {
                auto *list2 = as<FlowchartList>(values[2].value());
                for (auto &v: list2->values) {
                    if (equal_label_state(*const_as<FlowchartList>(v.value()),
                                          *const_as<FlowchartList>(values[0].value()),
                                          *const_as<FlowchartList>(values[3].value()))) {
                        return make_pair(true, values[1]);
                    }
                }
            }
            if (auto *list = as<FlowchartList>(values[1].value())) {
                as<FlowchartList>(values[0].value())->values[1] = FlowchartLabel(
                    string_from_literal_or_value(as<FlowchartList>(values[0].value())->values[1]));
                list->cons(values[0]);
                return make_pair(true, optional(*list));
            }
        } else if (op == "consUnique") {
            auto incoming_label = FlowchartLabel(string_from_literal_or_value(values[0]));
            if (values[1].has_value()) {
                auto *list = as<FlowchartList>(values[1].value());
                for (auto &v: list->values) {
                    if (equal_values(FlowchartLabel(string_from_literal_or_value(v)), incoming_label)) {
                        return make_pair(true, values[1]);
                    }
                }
            }
            if (auto *list = as<FlowchartList>(values[1].value())) {
                list->cons(incoming_label);
                return make_pair(true, optional(*list));
            }
        } else if (op == "usedVars") {
            return make_pair(true, optional(as<FlowchartProgram>(values[0].value())->get_used_vars()));
        }
    }
    throw std::runtime_error("Invalid expression");
}

string FlowchartProgramState::to_string() const {
    std::ostringstream oss;
    for (const auto &[key, value]: variables) {
        oss << key.name << " = " << value_to_string(value) << " $ ";
    }
    return oss.str();
}

bool Util::is_correct_value(const string &s) {
    return FlowchartLiteral::is_correct_string(s) ||
           FlowchartVariable::is_correct_string(s) ||
           FlowchartList::is_correct_string(s) ||
           FlowchartProgram::is_correct_string(s) ||
           FlowchartLabel::is_correct_string(s) ||
           FlowchartProgramState::is_correct_string(s) ||
           TuringMachineProgram::is_correct_string(s);
}

int main() {
    string input;
    cout << "Enter input file: ";
    cin >> input;

    ifstream ifs(input);

    string file;
    getline(ifs, file);
    FlowchartInterpreter::run_from_file(file, ifs);
}
