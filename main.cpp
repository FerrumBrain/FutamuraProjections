#include <iostream>
#include <fstream>
#include <map>
#include <numeric>
#include <regex>
#include <vector>
#include <string>
#include <stdexcept>
#include <sstream>

using namespace std;

class FlowchartProgramState;
class FlowchartBlock;
class Statement;
class FlowchartList;
class FlowchartProgram;
class TuringMachineProgram;

using FlowchartValue = std::variant<
    std::string,
    Statement,
    TuringMachineProgram,
    FlowchartBlock,
    FlowchartProgram,
    FlowchartList,
    FlowchartProgramState
>;

ifstream inputfs("/Users/Timur.Kudashev/CLionProjects/FlowchartFutamura/turing.in");

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

    static bool is_correct_var(const string &str) {
        return regex_match(str, regex(R"(^[a-zA-Z_][a-zA-Z0-9_]*$)"));
    }

    static bool is_correct_label(const string &str) {
        return regex_match(str, regex(R"(^[a-zA-Z_][a-zA-Z0-9_]*$)"));
    }

    static bool is_correct_const(const string &str) {
        return str == "'" || str.size() > 1 && str[0] == '\'' && regex_match(str.substr(1), regex(R"(^[^;\s]+$)"));
    }

    static bool is_correct_several_expr(const vector<string> &tokens, const int expected_number) {
        if (expected_number == 0) return tokens.empty();
        int balance = expected_number;
        for (size_t i = 0; i < tokens.size(); ++i) {
            if (functions.contains(tokens[i])) {
                balance += functions[tokens[i]] - 1;
            } else if (is_correct_var(tokens[i]) || is_correct_const(tokens[i])) {
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
        auto tokens = split_on_level(str, ' ', 0);

        if (functions.contains(tokens[0])) {
            return is_correct_several_expr(vector(tokens.begin() + 1, tokens.end()), functions[tokens[0]]);
        }

        if (tokens.size() == 1 && (is_correct_const(tokens[0]) || is_correct_var(tokens[0]))) return true;

        return false;
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
        if (tokens.size() == 2 && tokens[0] == "goto") {
            return is_correct_label(tokens[1]);
        }
        if (tokens.size() >= 2 && tokens[0] == "return") {
            std::string expr = join(1, tokens.size(), tokens, " ");
            return is_correct_expr(expr);
        }
        if (tokens.size() >= 6 && tokens[0] == "if" &&
            tokens[tokens.size() - 4] == "goto" &&
            tokens[tokens.size() - 2] == "else") {
            std::string cond = join(1, tokens.size() - 4, tokens, " ");
            return is_correct_expr(cond) &&
                   is_correct_label(tokens[tokens.size() - 3]) &&
                   is_correct_label(tokens[tokens.size() - 1]);
        }
        return false;
    }

    static bool is_correct_assignment(const string &str) {
        const auto tokens = split_on_level(str, ' ', 0);

        if (tokens.size() < 3 || tokens[0] != ":=") return false;

        const string expr = join(2, tokens.size(), tokens, " ");

        return is_correct_var(tokens[1]) && is_correct_expr(expr);
    }

    static string strip(const string &str, char c) {
        int start = 0;
        size_t end = str.size() - 1;
        while (str[start] == c) start++;
        while (str[end] == c) end--;
        return str.substr(start, end - start + 1);
    }
};

vector<char> Util::open_parenthesis = {'(', '[', '{'};

vector<char> Util::closed_parenthesis = {')', ']', '}'};

map<string, int> Util::functions = {
    {"inplaceTl", 0},

    {"hd", 1}, {"tl", 1}, {"firstInstruction", 1}, {"firstSym", 1}, {"firstCommand", 1}, {"rest", 1},
    {"lookupInitial", 1}, {"isEmpty", 1}, {"hasNext", 1}, {"inplaceCons", 1},

    {"==", 2}, {"cons", 2}, {"newTail", 2}, {"initialCode", 2}, {"eval", 2}, {"reduce", 2}, {"isStatic", 2},
    {"lookup", 2}, {"in", 2}, {"extendReturn", 2}, {"extendCode", 2}, {"nextLabel", 2},
    {"getLabel", 2}, {"parse", 2}, {"extendGoto", 2}, {"inplaceConsUniqueIfNotIn", 2},

    {"addToState", 3}, {"extendAssignment", 3}, {"consUniqueIfNotIn", 3}, {"ternaryOperator", 3},
    {"lookupStaticBounded", 3},

    {"extendIf", 5}
};

string value_to_string(optional<FlowchartValue> value);

template<typename T>
T *as(FlowchartValue &value);

optional<string> boolean_to_optional_string(const bool value) {
    return value ? optional("true") : optional("false");
}

class Statement {
    std::vector<std::string> elems;
    bool split_by_spaces;
    bool split_by_expr;

public:
    explicit Statement(const std::vector<std::string> &elems = {}, const std::string &code = "",
                       const bool split_by_spaces = false,
                       const bool split_by_expr = false): split_by_spaces(split_by_spaces),
                                                          split_by_expr(split_by_expr) {
        if (elems.empty()) {
            this->elems.clear();
            if (!code.empty()) {
                if (split_by_spaces) {
                    for (const auto &token: Util::split_on_level(Util::strip(code, ';'), ' ', 0)) {
                        this->elems.emplace_back(Util::strip(token, ' '));
                    }
                } else if (split_by_expr) {
                    vector<string> tokens;
                    for (const auto &token: Util::split_on_level(Util::strip(code, ';'), ' ', 0)) {
                        tokens.emplace_back(Util::strip(token, ' '));
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

    [[nodiscard]] std::optional<std::string> head() const {
        return elems.empty() ? nullopt : optional(elems[0]);
    }

    [[nodiscard]] Statement tail() const {
        if (elems.size() <= 1) return Statement({}, "", split_by_spaces, split_by_expr);
        return Statement(std::vector(elems.begin() + 1, elems.end()), "", split_by_spaces, split_by_expr);
    }

    void cons(const std::string &element) {
        elems.insert(elems.begin(), element);
    }

    [[nodiscard]] bool is_empty() const {
        return elems.empty();
    }

    bool operator==(const Statement &other) const {
        return elems == other.elems;
    }

    [[nodiscard]] std::string to_string() const {
        return Util::join(0, elems.size(), elems, " ");
    }
};

class TuringMachineProgram {
public:
    map<string, Statement> dictionary;
    std::vector<string> order;

    TuringMachineProgram(const string &keys_values, const map<string, Statement> &dictionary,
                         const std::vector<string> &order) {
        this->dictionary = {};
        this->order = {};
        if (keys_values.empty()) {
            this->dictionary = dictionary;
            this->order = order;
        } else {
            if (keys_values != "{}") {
                for (const vector<string> keys_values_split = Util::split_on_level(
                         keys_values.substr(1, keys_values.size() - 2), '$',
                         0); const auto &key_value: keys_values_split) {
                    const auto tokens = Util::split_on_level(key_value, ':', 0);
                    this->dictionary[Util::strip(tokens[0], ' ')] = Statement(
                        {}, Util::strip(tokens[1], ' '), true, false);
                    this->order.emplace_back(Util::strip(tokens[0], ' '));
                }
            }
        }
    }

    static bool is_correct_string(const std::string &str) {
        return !str.empty() && str.front() == '{' && str.back() == '}';
    }

    [[nodiscard]] bool is_empty() const {
        return order.empty();
    }

    bool operator==(const TuringMachineProgram &other) const {
        return order == other.order && dictionary == other.dictionary;
    }

    [[nodiscard]] std::string to_string() {
        std::ostringstream oss;
        oss << "'{";
        for (size_t i = 0; i < order.size(); ++i) {
            if (i > 0) oss << " $ ";
            oss << order[i] << ": " << dictionary[order[i]].to_string();
        }
        oss << "}";
        return oss.str();
    }
};

optional<FlowchartValue> value_from_raw(const string &raw, optional<FlowchartProgramState> state, bool is_reduce);

class FlowchartBlock {
    std::string label;
    std::vector<Statement> contents;

public:
    explicit FlowchartBlock(std::string label = "", std::vector<Statement> contents = {})
        : label(std::move(label)), contents(std::move(contents)) {
    }

    void add_line(const std::string &line) {
        contents.emplace_back(Statement{{}, line, false, true});
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
        if (contents.size() < 2) {
            return FlowchartBlock{label, {}};
        }
        return FlowchartBlock{label, std::vector(contents.begin() + 1, contents.end())};
    }

    [[nodiscard]] std::string to_string() const {
        std::ostringstream oss;
        oss << label << ":\n";
        for (auto &line: contents) {
            oss << "    " << line.to_string() << ";\n";
        }
        return oss.str();
    }
};

class FlowchartProgramState {
public:
    map<string, optional<FlowchartValue> > variables;

    FlowchartProgramState(const optional<FlowchartProgramState> &parent_state, bool is_reduce, const string &s);

    [[nodiscard]] bool is_empty() const;

    bool operator==(const FlowchartProgramState &other) const;

    static bool is_static(const FlowchartList &division, const string &expr);

    static bool is_correct_string(const string &s) {
        return !s.empty() && s.front() == '[' && s.back() == ']';
    }

    void append(const string &name, const optional<FlowchartValue> &value);

    optional<FlowchartValue> evaluate(const string &expr);

    optional<FlowchartValue> reduce(const string &expr);

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

    string to_string();

    pair<bool, optional<FlowchartValue> > eval_expr(const string &expr, bool is_reduce, int op_index);
};

class FlowchartList {
    std::optional<FlowchartProgramState> state;

public:
    std::vector<optional<FlowchartValue> > values;

    FlowchartList(const std::optional<FlowchartProgramState> &state, bool isReduce, const std::string &s,
                  const optional<vector<optional<FlowchartValue> > > &values);

    static bool is_correct_string(const std::string &str) {
        return !str.empty() && str.front() == '(' && str.back() == ')';
    }

    [[nodiscard]] optional<FlowchartValue> head() const;

    [[nodiscard]] FlowchartList tail() const;

    void cons(const optional<FlowchartValue> &elem);

    [[nodiscard]] bool is_empty() const;

    void update(const string &op, const vector<optional<FlowchartValue> > &exprs);

    bool operator==(const FlowchartList &other) const;

    [[nodiscard]] std::string to_string() const;
};

class FlowchartProgram {
    map<string, FlowchartBlock> blocks;
    bool is_reduce;
    optional<FlowchartProgramState> parent_state;
    int lookup_id = 0;
    string program;

public:
    vector<string> labels;
    FlowchartProgramState state;

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

    static bool is_correct_string(const string &str) {
        auto lines = vector<string>{};
        for (const auto &line: Util::split_on_level(Util::strip(str, ' '), ';', 0)) {
            lines.emplace_back(Util::strip(line, ' '));
        }
        int i = 0;
        if (lines[0].rfind("read") == 0) {
            for (const auto tokens = Util::split_on_level(lines[0].substr(4), ',', 0); const auto &token: tokens) {
                if (!Util::is_correct_var(Util::strip(token, ' ')))
                    return false;
            }
            i++;
        }
        while (i < lines.size()) {
            const auto raw_tokens = Util::split_on_level(lines[i], ':', 0);
            vector<string> tokens;
            tokens.reserve(raw_tokens.size());
            for (const auto &token: raw_tokens) {
                tokens.emplace_back(Util::strip(token, ' '));
            }
            string label = Util::strip(tokens[0], ' ');
            string line = Util::join(1, tokens.size(), tokens, ":");

            if (!Util::is_correct_label(label))
                return false;
            while (!Util::is_correct_jump(line)) {
                if (!Util::is_correct_assignment(line))
                    return false;
                i++;
                line = lines[i];
            }
            i++;
        }
        return true;
    }

    FlowchartProgram parse_program(const bool read_from_input, const optional<FlowchartProgramState> &state) {
        auto lines = vector<string>{};
        for (const auto &line: Util::split_on_level(Util::strip(program, ' '), ';', 0)) {
            lines.emplace_back(Util::strip(line, ' '));
        }
        auto result = FlowchartProgram(parent_state, is_reduce, program, "");
        int i = 0;
        if (lines[0].rfind("read") == 0) {
            for (const auto tokens = Util::split_on_level(lines[0].substr(4), ',', 0); const auto &token: tokens) {
                string key = Util::strip(token, ' ');
                if (read_from_input) {
                    std::string input;
                    getline(inputfs, input);
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
                tokens.emplace_back(Util::strip(token, ' '));
            }
            string label = Util::strip(tokens[0], ' ');
            string line = Util::join(1, tokens.size(), tokens, ":");

            result.labels.emplace_back(label);
            result.blocks[label] = FlowchartBlock(label, {});
            while (!Util::is_correct_jump(line)) {
                if (line.rfind(" parse ") != string::npos) {
                    auto args = Util::split_on_level(Util::strip(line, ' '), ' ', 0);
                    const string &parsed_program_arg = args[1];
                    auto program_arg = as<FlowchartProgram>(result.state.variables[args[3]].value());
                    const string &vs_arg = args[4];
                    if (result.state.variables.contains(vs_arg)) {
                        if (!result.state.variables[vs_arg].has_value())
                            result.state.variables[parsed_program_arg] = program_arg->parse_program(false, nullopt);
                        else
                            result.state.variables[parsed_program_arg] = program_arg->parse_program(
                                false, *as<FlowchartProgramState>(result.state.variables[vs_arg].value()));
                    } else
                        result.state.variables[parsed_program_arg] = program_arg->parse_program(false, nullopt);
                    if (result.state.variables.contains(vs_arg) && result.state.variables[vs_arg].has_value() && as<
                            FlowchartProgramState>(result.state.variables[vs_arg].value())->variables.contains(
                            parsed_program_arg))
                        as<FlowchartProgramState>(result.state.variables[vs_arg].value())->variables[parsed_program_arg]
                                = result.state.variables[parsed_program_arg];
                } else if (line.rfind(" lookupStaticBounded ") != string::npos) {
                    result.lookup_id++;
                    auto line_without_spaces = line;
                    ranges::replace(line_without_spaces, ' ', '_');
                    const string &after_lookup_label =
                            "after_" + std::to_string(result.lookup_id) + "_" + line_without_spaces;
                    const string &start_lookup_label =
                            "start_" + std::to_string(result.lookup_id) + "_" + line_without_spaces;
                    const string &continue_lookup_label =
                            "continue_" + std::to_string(result.lookup_id) + "_" + line_without_spaces;
                    auto args = Util::split_on_level(Util::strip(line, ' '), ' ', 0);
                    const auto &bb_arg = args[1];
                    const auto &pp_arg = args[3];
                    const auto &program_arg = args[4];
                    const auto &ppi_arg = args[5];
                    result.blocks[label].add_line("goto " + start_lookup_label + ";");

                    result.labels.emplace_back(start_lookup_label);
                    result.blocks[start_lookup_label] = FlowchartBlock(start_lookup_label, {});
                    result.blocks[start_lookup_label].add_line(":= " + ppi_arg + " lookupInitial " + program_arg + ";");
                    result.blocks[start_lookup_label].add_line(
                        ":= " + bb_arg + " lookup " + ppi_arg + " " + program_arg + ";");
                    result.blocks[start_lookup_label].add_line(
                        "if == " + ppi_arg + " " + pp_arg + " goto " + after_lookup_label + " else " +
                        continue_lookup_label + ";");

                    result.labels.emplace_back(continue_lookup_label);
                    result.blocks[continue_lookup_label] = FlowchartBlock(continue_lookup_label, {});
                    result.blocks[continue_lookup_label].add_line(
                        ":= " + ppi_arg + " nextLabel " + ppi_arg + " " + program_arg + ";");
                    result.blocks[continue_lookup_label].add_line(
                        ":= " + bb_arg + " lookup " + ppi_arg + " " + program_arg + ";");
                    result.blocks[continue_lookup_label].add_line(
                        "if == " + ppi_arg + " " + pp_arg + " goto " + after_lookup_label + " else " +
                        continue_lookup_label + ";");

                    result.labels.emplace_back(after_lookup_label);
                    result.blocks[after_lookup_label] = FlowchartBlock(after_lookup_label, {});
                    label = after_lookup_label;
                } else {
                    result.blocks[label].add_line(line);
                }

                i++;
                line = lines[i];
            }
            result.blocks[label].add_line(line);
            i++;
        }
        return result;
    }

    FlowchartBlock get_block(const string &label) {
        return blocks[label];
    }

    bool has_next(const string &label) {
        return ranges::find(labels, label) != labels.end();
    }

    string get_label(const int index) {
        return labels[index];
    }

    string next_label(const string &label) {
        const size_t index = ranges::find(labels, label) - labels.begin();
        return labels[index + 1];
    }

    [[nodiscard]] std::string to_string() const {
        std::ostringstream oss;
        for (const auto &label: labels) {
            oss << blocks.at(label).to_string() << "\n";
        }
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
        if (auto *v = as<Statement>(value.value())) {
            return v->to_string();
        }
        if (auto *v = as<FlowchartBlock>(value.value())) {
            return v->to_string();
        }
        if (auto *v = as<FlowchartProgram>(value.value())) {
            return v->to_string();
        }
        if (auto *v = as<FlowchartProgramState>(value.value())) {
            return v->to_string();
        }
        if (auto *v = as<FlowchartList>(value.value())) {
            return v->to_string();
        }
        if (auto *v = as<TuringMachineProgram>(value.value())) {
            return v->to_string();
        }
        if (auto *v = as<string>(value.value())) {
            return *v;
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
            if (value_to_string(v) == tokens[0]) {
                found = true;
                break;
            }
        }
        if (found)
            return true;
        if (!tokens.empty() && tokens[0][0] == '\'')
            return true;
        return false;
    }

    return ranges::all_of(split_to_expr(vector(tokens.begin() + 1, tokens.end()), Util::functions[tokens[0]]),
                          [&](const string &s) { return is_static(division, s); });
}

optional<FlowchartValue>
value_from_raw(const string &raw, optional<FlowchartProgramState> state, const bool is_reduce) {
    string s = Util::strip(raw, ' ');
    if (s.empty()) return string("");
    if (FlowchartList::is_correct_string(s)) return FlowchartList(state, is_reduce, s, {});
    if (TuringMachineProgram::is_correct_string(s)) return TuringMachineProgram(s, {}, {});
    if (FlowchartProgramState::is_correct_string(s)) return FlowchartProgramState(state, is_reduce, s);
    if (FlowchartProgram::is_correct_string(s)) return FlowchartProgram(state, is_reduce, s, "");
    if (state.has_value()) return state.value().eval_expr(s, is_reduce, 0).second;
    return s;
}

class FlowchartInterpreter {
    FlowchartProgram program;

    std::optional<std::string> execute_block(const std::string &label) {
        auto block = program.get_block(label);
        size_t i = 0;

        while (i < block.size()) {
            auto tokens = Util::split_on_level(block.get_line(i)->to_string(), ' ', 0);
            if (tokens[0] == ":=") {
                if (tokens[2].size() > 7 && tokens[2].substr(0, 7) == "inplace") {
                    std::string expr = Util::join(1, tokens.size(), tokens, " ");
                    program.state.eval_expr(expr, false, 1).second;
                } else {
                    std::string expr = Util::join(2, tokens.size(), tokens, " ");
                    program.state.variables[tokens[1]] = program.state.eval_expr(expr, false, 0).second;
                }
            } else if (tokens[0] == "goto") {
                return tokens[1];
            } else if (tokens[0] == "if") {
                std::string cond = Util::join(1, tokens.size() - 4, tokens, " "),
                        true_label = tokens[tokens.size() - 3], false_label = tokens[tokens.size() - 1];
                auto result = program.state.eval_expr(cond, false, 0).second.value();
                return *as<string>(result) == "true" ? true_label : false_label;
            } else if (tokens[0] == "return") {
                auto result = program.state.eval_expr(Util::join(1, tokens.size(), tokens, " "), false, 0).second;
                string output = value_to_string(result);
                std::cout << "Returned:" << std::endl << output << std::endl;
                return nullopt;
            } else {
                throw std::runtime_error("Unexpected statement");
            }
            i++;
        }
        return nullopt;
    }

    void run() {
        int label_counter = 1;
        std::optional current_label = program.get_label(0);
        while (current_label.has_value()) {
            current_label = execute_block(current_label.value());
            label_counter++;
            if (current_label.has_value() && current_label.value() == "do_if_dynamic") {
                cout << "aboba\n";
            }
            if (label_counter % 1 == 0) {
                cout << label_counter << ": " << current_label.value_or("the end") << endl;
            }
        }
    }

    FlowchartInterpreter(const std::string &program_data, const std::string &filename)
        : program(nullopt, false, program_data, filename) {
        program = program.parse_program(true, nullopt);
    }

public:
    static void run_from_file(const std::string &filename) {
        FlowchartInterpreter interpreter("", filename);
        interpreter.run();
    }

    static void run_from_program(const std::string &program) {
        FlowchartInterpreter interpreter(program, "");
        interpreter.run();
    }
};

FlowchartProgramState::FlowchartProgramState(const optional<FlowchartProgramState> &parent_state, const bool is_reduce,
                                             const string &s) {
    this->variables = {};
    if (!s.empty() && s != "[]") {
        const auto tmp = Util::split_on_level(s.substr(1, s.size() - 2), '$', 0);
        for (int i = 0; i < tmp.size(); i += 2) {
            variables[Util::strip(tmp[i], ' ')] = value_from_raw(Util::strip(tmp[i + 1], ' '), parent_state, is_reduce);
        }
    }
}

bool FlowchartProgramState::is_empty() const {
    return variables.empty();
}


bool equal_values(const optional<FlowchartValue> &a, const optional<FlowchartValue> &b) {
    if (a.has_value() != b.has_value()) return false;
    if (!a.has_value()) return true;
    if (auto *stmt1 = const_as<Statement>(a.value())) {
        if (auto *stmt2 = const_as<Statement>(b.value())) {
            return *stmt1 == *stmt2;
        }
        return false;
    }
    if (auto *stmt1 = const_as<TuringMachineProgram>(a.value())) {
        if (auto *stmt2 = const_as<TuringMachineProgram>(b.value())) {
            return *stmt1 == *stmt2;
        }
        return false;
    }
    if (auto *stmt1 = const_as<string>(a.value())) {
        if (auto *stmt2 = const_as<string>(b.value())) {
            return *stmt1 == *stmt2;
        }
        return false;
    }
    if (auto *stmt1 = const_as<FlowchartBlock>(a.value())) {
        if (auto *stmt2 = const_as<FlowchartBlock>(b.value())) {
            return *stmt1 == *stmt2;
        }
        return false;
    }
    if (auto *stmt1 = const_as<FlowchartProgramState>(a.value())) {
        if (auto *stmt2 = const_as<FlowchartProgramState>(b.value())) {
            return *stmt1 == *stmt2;
        }
        return false;
    }
    if (auto *stmt1 = const_as<FlowchartProgram>(a.value())) {
        if (auto *stmt2 = const_as<FlowchartProgram>(b.value())) {
            return stmt1->to_string() == stmt2->to_string();
        }
        return false;
    }
    if (auto *stmt1 = const_as<FlowchartList>(a.value())) {
        if (auto *stmt2 = const_as<FlowchartList>(b.value())) {
            return *stmt1 == *stmt2;
        }
        return false;
    }
    throw runtime_error("FlowchartList::equal_values() failed");
}

bool FlowchartProgramState::operator==(const FlowchartProgramState &other) const {
    if (variables.size() != other.variables.size()) return false;
    for (auto [key, value]: variables) {
        if (!other.variables.contains(key)) return false;
        if (value.has_value() != other.variables.at(key).has_value()) return false;
        if (!value.has_value()) continue;

        if (!equal_values(value, other.variables.at(key))) return false;
    }
    return true;
}

void FlowchartProgramState::append(const string &name, const optional<FlowchartValue> &value) {
    variables[name] = value;
}

optional<FlowchartValue> FlowchartProgramState::evaluate(const string &expr) {
    return eval_expr(expr, false, 0).second;
}

optional<FlowchartValue> FlowchartProgramState::reduce(const string &expr) {
    return eval_expr(expr, true, 0).second;
}

FlowchartList::FlowchartList(const std::optional<FlowchartProgramState> &state, const bool isReduce,
                             const std::string &s,
                             const optional<std::vector<optional<FlowchartValue> > > &values): state(state) {
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

[[nodiscard]] optional<FlowchartValue> FlowchartList::head() const {
    return values.empty() ? nullopt : optional(values.back());
}

[[nodiscard]] FlowchartList FlowchartList::tail() const {
    return values.size() < 2
               ? FlowchartList(state, false, "", optional(vector<optional<FlowchartValue> >{}))
               : FlowchartList(state, false, "", vector(values.begin(), values.end() - 1));
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

[[nodiscard]] std::string FlowchartList::to_string() const {
    std::ostringstream oss;
    oss << "'(";
    for (size_t i = 0; i < values.size(); ++i) {
        if (i > 0) oss << " $ ";
        oss << value_to_string(values[values.size() - 1 - i]);
    }
    oss << ")";
    return oss.str();
}

pair<bool, optional<FlowchartValue> >
FlowchartProgramState::eval_expr(const string &expr, bool is_reduce, int op_index) {
    auto tokens = Util::split_on_level(expr, ' ', 0);
    if (tokens.size() == 1) {
        if (variables.contains(tokens[0])) {
            return make_pair(true, variables[tokens[0]]);
        }
        if (tokens[0][0] == '\'') {
            if (tokens[0].size() == 1 || ranges::find(Util::open_parenthesis, tokens[0][1]) == Util::open_parenthesis.
                end()) {
                return make_pair(true, value_from_raw(tokens[0].substr(1), nullopt, is_reduce));
            }
            return make_pair(true, value_from_raw(tokens[0].substr(1), *this, is_reduce));
        }
        if (is_reduce) {
            return make_pair(false, expr);
        }
        throw std::runtime_error("Invalid expression");
    }

    if (string op = tokens[op_index]; Util::functions.contains(op)) {
        vector<string> relevant_tokens = {};
        for (int i = 0; i < tokens.size(); i++) {
            if (i == op_index) continue;
            relevant_tokens.emplace_back(tokens[i]);
        }
        auto args = split_to_expr(relevant_tokens, Util::functions[op] + op_index);
        bool success = true;
        vector<optional<FlowchartValue> > values;
        vector<bool> s;
        for (const auto &arg: args) {
            const auto [r, v] = eval_expr(arg, is_reduce, 0);
            success = success && r;
            values.emplace_back(v);
            s.emplace_back(r);
        }
        if (!success) {
            string reduced;
            for (int i = 0; i < values.size(); ++i) {
                if (s[i]) reduced += "'";
                reduced += value_to_string(values[i]);
                reduced += " ";
            }
            return make_pair(false, optional(op + " " + reduced));
        }
        if (op == "hd") {
            if (!values[0].has_value())
                return make_pair(true, nullopt);

            if (auto *stmt = as<Statement>(values[0].value())) {
                return make_pair(true, optional(stmt->head()));
            }
            if (auto *list = as<FlowchartList>(values[0].value())) {
                return make_pair(true, optional(list->head()));
            }
        } else if (op == "tl") {
            if (!values[0].has_value())
                return make_pair(true, nullopt);

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
            if (!values[0].has_value())
                return make_pair(true, nullopt);

            if (auto *stmt = as<Statement>(values[1].value())) {
                stmt->cons(value_to_string(values[0]));
                return make_pair(true, optional(*stmt));
            }
            if (auto *list = as<FlowchartList>(values[1].value())) {
                list->cons(values[0]);
                return make_pair(true, optional(*list));
            }
        } else if (op == "==") {
            return make_pair(true, boolean_to_optional_string(equal_values(values[0], values[1])));
        } else if (op == "newTail") {
            if (!values[0].has_value() || !values[1].has_value())
                return make_pair(true, nullopt);

            auto *tm_program = as<TuringMachineProgram>(values[1].value());
            auto dictionary = tm_program->dictionary;
            auto order = tm_program->order;
            string label = value_to_string(values[0]);
            int index = 0;
            for (; index < order.size(); index++) {
                if (order[index] == label) break;
            }
            auto new_order = vector(order.begin() + index, order.end());
            map<string, Statement> new_dictionary = {};
            for (const auto &k: new_order) {
                new_dictionary[k] = dictionary[k];
            }
            return make_pair(true, optional(TuringMachineProgram("", new_dictionary, new_order)));
        } else if (op == "firstInstruction") {
            if (!values[0].has_value()) return make_pair(true, nullopt);

            auto *tm_program = as<TuringMachineProgram>(values[0].value());
            auto dictionary = tm_program->dictionary;
            auto order = tm_program->order;
            return make_pair(true, optional(dictionary[order[0]]));
        } else if (op == "firstSym") {
            if (!values[0].has_value()) return make_pair(true, optional(""));

            auto *list = as<FlowchartList>(values[0].value());
            return make_pair(true, list->head());
        } else if (op == "firstCommand") {
            if (!values[0].has_value()) return make_pair(true, nullopt);

            auto *block = as<FlowchartBlock>(values[0].value());
            return make_pair(true, block->get_line(0));
        } else if (op == "rest") {
            if (!values[0].has_value()) return make_pair(true, nullopt);

            auto *tm_program = as<TuringMachineProgram>(values[0].value());
            auto dictionary = tm_program->dictionary;
            auto order = tm_program->order;
            auto new_order = vector(order.begin() + 1, order.end());
            map<string, Statement> new_dictionary = {};
            for (const auto &k: new_order) {
                new_dictionary[k] = dictionary[k];
            }
            return make_pair(true, optional(TuringMachineProgram("", new_dictionary, new_order)));
        } else if (op == "initialCode") {
            string label = value_to_string(values[0]) + "_" + value_to_string(values[1]) + ":\n";
            ranges::replace(label, ' ', '_');
            return make_pair(true, optional(label));
        } else if (op == "extendIf") {
            string true_label = value_to_string(values[2]) + "_" + value_to_string(values[4]);
            ranges::replace(true_label, ' ', '_');
            string false_label = value_to_string(values[3]) + "_" + value_to_string(values[4]);
            ranges::replace(false_label, ' ', '_');
            return make_pair(true, optional(
                                 value_to_string(values[0]) + "if " + value_to_string(values[1]) + " goto " + true_label
                                 + " else " + false_label + ";\n"));
        } else if (op == "extendReturn") {
            return make_pair(true, value_to_string(values[0]) + "return " + value_to_string(values[1]) + ";\n");
        } else if (op == "extendGoto") {
            return make_pair(true, value_to_string(values[0]) + "goto " + value_to_string(values[1]) + ";\n");
        } else if (op == "extendAssignment") {
            return make_pair(true, optional(
                                 value_to_string(values[0]) + ":= " + value_to_string(values[1]) + " " +
                                 value_to_string(values[2]) + ";\n"));
        } else if (op == "extendCode") {
            return make_pair(true, optional(value_to_string(values[0]) + value_to_string(values[1])));
        } else if (op == "eval") {
            auto *program_state = as<FlowchartProgramState>(values[1].value());
            return make_pair(true, program_state->evaluate(value_to_string(values[0])));
        } else if (op == "reduce") {
            auto *program_state = as<FlowchartProgramState>(values[1].value());
            return make_pair(true, program_state->reduce(value_to_string(values[0])));
        } else if (op == "addToState") {
            auto *program_state = as<FlowchartProgramState>(values[0].value());
            program_state->append(value_to_string(values[1]), values[2]);
            return make_pair(true, optional(*program_state));
        } else if (op == "isStatic") {
            return make_pair(true, boolean_to_optional_string(
                                 is_static(*as<FlowchartList>(values[0].value()), value_to_string(values[1]))
                             ));
        } else if (op == "lookup") {
            auto *program = as<FlowchartProgram>(values[1].value());
            return make_pair(true, optional(program->get_block(value_to_string(values[0]))));
        } else if (op == "in") {
            auto *list = as<FlowchartList>(values[1].value());
            for (optional<FlowchartValue> &v: list->values) {
                if (equal_values(v, values[0])) {
                    return make_pair(true, boolean_to_optional_string(true));
                }
            }
            return make_pair(true, boolean_to_optional_string(false));
        } else if (op == "lookupInitial") {
            auto *program = as<FlowchartProgram>(values[0].value());
            return make_pair(true, optional(program->labels[0]));
        } else if (op == "isEmpty") {
            if (!values[0].has_value()) return make_pair(true, boolean_to_optional_string(true));
            return make_pair(true, boolean_to_optional_string(as<FlowchartBlock>(values[0].value())->size() == 0));
        } else if (op == "nextLabel") {
            auto *program = as<FlowchartProgram>(values[1].value());
            return make_pair(true, program->next_label(value_to_string(values[0])));
        } else if (op == "getLabel") {
            auto *program = as<FlowchartProgram>(values[1].value());
            return make_pair(true, program->get_label(stoi(value_to_string(values[0]))));
        } else if (op == "hasNext") {
            auto *program = as<FlowchartProgram>(values[1].value());
            return make_pair(true, boolean_to_optional_string(program->has_next(value_to_string(values[0]))));
        } else if (op == "ternaryOperator") {
            if (value_to_string(values[0]) == "true") return make_pair(true, values[1]);
            return make_pair(true, values[2]);
        } else if (op == "consUniqueIfNotIn") {
            if (values[1].has_value()) {
                auto *list = as<FlowchartList>(values[1].value());
                for (auto &v: list->values) {
                    if (equal_values(v, values[0])) {
                        return make_pair(true, values[1]);
                    }
                }
            }
            if (values[2].has_value()) {
                auto *list2 = as<FlowchartList>(values[2].value());
                for (auto &v: list2->values) {
                    if (equal_values(v, values[0])) {
                        return make_pair(true, values[1]);
                    }
                }
            }
            if (auto *stmt = as<Statement>(values[1].value())) {
                stmt->cons(value_to_string(values[0]));
                return make_pair(true, optional(*stmt));
            }
            if (auto *list = as<FlowchartList>(values[1].value())) {
                list->cons(values[0]);
                return make_pair(true, optional(*list));
            }
        } else if (op == "inplaceTl") {
            if (!variables[args[0]].has_value()) {
                return make_pair(true, nullopt);
            }
            as<FlowchartList>(variables[args[0]].value())->values.pop_back();
            return make_pair(true, nullopt);
        } else if (op == "inplaceCons") {
            if (!variables[args[0]].has_value()) {
                variables[args[0]] = FlowchartList(nullopt, is_reduce, "", {});
            }
            as<FlowchartList>(variables[args[0]].value())->values.emplace_back(values[1]);
            return make_pair(true, nullopt);
        } else if (op == "inplaceConsUniqueIfNotIn") {
            if (!variables[args[0]].has_value()) {
                variables[args[0]] = FlowchartList(nullopt, is_reduce, "", {});
            }
            auto *list = as<FlowchartList>(variables[args[0]].value());
            for (auto &v: list->values) {
                if (equal_values(v, values[1])) {
                    return make_pair(true, nullopt);
                }
            }
            if (values[2].has_value()) {
                auto *list2 = as<FlowchartList>(values[2].value());
                for (auto &v: list2->values) {
                    if (equal_values(v, values[1])) {
                        return make_pair(true, nullopt);
                    }
                }
            }
            as<FlowchartList>(variables[args[0]].value())->values.emplace_back(values[1]);
            return make_pair(true, nullopt);
        }
    }
    throw std::runtime_error("Invalid expression");
}

string FlowchartProgramState::to_string() {
    std::ostringstream oss;
    for (const auto &[key, value]: variables) {
        oss << key << "=" << value_to_string(value) << " ";
    }
    return oss.str();
}

int main() {
    string file;
    getline(inputfs, file);
    FlowchartInterpreter::run_from_file(file);
}
