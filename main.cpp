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

ifstream inputfs("/Users/Timur.Kudashev/CLionProjects/FlowchartFutamura/mix_mix.in");
bool enableLogging = false;

void replaceAll(std::string& str, const std::string& from, const std::string& to) {
    size_t start_pos = 0;
    while ((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length();
    }
}

long long current_time() {
    static long long last_time = 0;
    auto result = std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::system_clock::now().time_since_epoch()).count();
    auto last_time_copy = last_time;
    last_time = result;
    return result - last_time_copy;
}

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
        return regex_match(strip_spaces(str), regex(R"(^[a-zA-Z_][a-zA-Z0-9_]*$)"));
    }

    static bool is_correct_label(const string &str) {
        return regex_match(strip_spaces(str), regex(R"(^\S+$)"));
    }

    static bool is_correct_const(const string &s) {
        string str = strip_spaces(s);
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
        auto tokens = split_on_level(strip_spaces(str), ' ', 0);

        if (functions.contains(tokens[0])) {
            if (tokens.size() != functions[tokens[0]] + 1) return false;
            for (int i = 1; i < tokens.size(); ++i) {
                if (!is_correct_var(tokens[i])) return false;
            }
            return true;
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
        if (tokens.size() == 2 && strip_spaces(tokens[0]) == "goto") {
            return is_correct_label(tokens[1]);
        }
        if (tokens.size() >= 2 && strip_spaces(tokens[0]) == "return") {
            std::string expr = join(1, tokens.size(), tokens, " ");
            return is_correct_var(expr);
        }
        if (tokens.size() >= 6 && strip_spaces(tokens[0]) == "if" &&
            strip_spaces(tokens[tokens.size() - 4]) == "goto" &&
            strip_spaces(tokens[tokens.size() - 2]) == "else") {
            std::string cond = join(1, tokens.size() - 4, tokens, " ");
            return is_correct_var(cond) &&
                   is_correct_label(tokens[tokens.size() - 3]) &&
                   is_correct_label(tokens[tokens.size() - 1]);
        }
        return false;
    }

    static bool is_correct_assignment(const string &str) {
        const auto tokens = split_on_level(strip_spaces(str), ' ', 0);

        if (tokens.size() < 3 || strip_spaces(tokens[0]) != ":=") return false;

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

    static string strip_spaces(const string &str) {
        return strip(strip(strip(str, '\t'), '\n'), ' ');
    }
};

vector<char> Util::open_parenthesis = {'(', '[', '{'};

vector<char> Util::closed_parenthesis = {')', ']', '}'};

map<string, int> Util::functions = {
    {"hd", 1}, {"tl", 1}, {"firstInstruction", 1}, {"firstSym", 1}, {"firstCommand", 1}, {"rest", 1},
    {"lookupInitial", 1}, {"isEmpty", 1},

    {"hasNext", 2}, {"==", 2}, {"cons", 2}, {"newTail", 2}, {"initialCode", 2}, {"eval", 2}, {"reduce", 2},
    {"isStatic", 2},
    {"lookup", 2}, {"in", 2}, {"extendReturn", 2}, {"extendCode", 2}, {"nextLabel", 2},
    {"getLabel", 2}, {"parse", 2}, {"extendGoto", 2},

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
        if (enableLogging) cout << "Statement: Start: " << current_time() << endl;
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
        if (enableLogging) cout << "Statement: End: " << current_time() << endl;
    }

    [[nodiscard]] std::optional<std::string> head() const {
        if (enableLogging) cout << "Statement.head: Start: " << current_time() << endl;
        const auto &result = elems.empty() ? nullopt : optional(elems[0]);
        if (enableLogging) cout << "Statement.head: End: " << current_time() << endl;
        return result;
    }

    [[nodiscard]] Statement tail() const {
        if (enableLogging) cout << "Statement.tail: Start: " << current_time() << endl;
        const auto &result = elems.size() <= 1
                                 ? Statement({}, "", split_by_spaces, split_by_expr)
                                 : Statement(std::vector(elems.begin() + 1, elems.end()), "", split_by_spaces,
                                             split_by_expr);
        if (enableLogging) cout << "Statement.tail: End: " << current_time() << endl;
        return result;
    }

    void cons(const std::string &element) {
        if (enableLogging) cout << "Statement.cons: Start: " << current_time() << endl;
        elems.insert(elems.begin(), element);
        if (enableLogging) cout << "Statement.cons: End: " << current_time() << endl;
    }

    [[nodiscard]] bool is_empty() const {
        return elems.empty();
    }

    bool operator==(const Statement &other) const {
        if (enableLogging) cout << "Statement.==: Start: " << current_time() << endl;
        bool result = elems == other.elems;
        if (enableLogging) cout << "Statement.==: End: " << current_time() << endl;
        return result;
    }

    [[nodiscard]] std::string to_string() const {
        if (enableLogging) cout << "Statement.to_string: Start: " << current_time() << endl;
        string s = Util::join(0, elems.size(), elems, " ");
        if (enableLogging) cout << "Statement.to_string: End: " << current_time() << endl;
        return s;
    }
};

class TuringMachineProgram {
public:
    map<string, Statement> dictionary;
    std::vector<string> order;

    TuringMachineProgram(const string &keys_values, const map<string, Statement> &dictionary,
                         const std::vector<string> &order) {
        if (enableLogging) cout << "TuringMachineProgram: Start: " << current_time() << endl;
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
                    this->dictionary[Util::strip_spaces(tokens[0])] = Statement(
                        {}, Util::strip_spaces(tokens[1]), true, false);
                    this->order.emplace_back(Util::strip_spaces(tokens[0]));
                }
            }
        }
        if (enableLogging) cout << "TuringMachineProgram: End: " << current_time() << endl;
    }

    static bool is_correct_string(const std::string &str) {
        return !str.empty() && str.front() == '{' && str.back() == '}';
    }

    [[nodiscard]] bool is_empty() const {
        return order.empty();
    }

    bool operator==(const TuringMachineProgram &other) const {
        if (enableLogging) cout << "TuringMachineProgram.==: Start: " << current_time() << endl;
        bool result = order == other.order && dictionary == other.dictionary;
        if (enableLogging) cout << "TuringMachineProgram.==: End: " << current_time() << endl;
        return result;
    }

    [[nodiscard]] std::string to_string() {
        if (enableLogging) cout << "TuringMachineProgram.to_string: Start: " << current_time() << endl;
        std::ostringstream oss;
        oss << "{";
        for (size_t i = 0; i < order.size(); ++i) {
            if (i > 0) oss << " $ ";
            oss << order[i] << ": " << dictionary[order[i]].to_string();
        }
        oss << "}";
        if (enableLogging) cout << "TuringMachineProgram.to_string: End: " << current_time() << endl;
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
        if (enableLogging) cout << "FlowchartBlock.get_line: Start: " << current_time() << endl;
        auto result = index >= contents.size() ? nullopt : optional(contents[index]);
        if (enableLogging) cout << "FlowchartBlock.get_line: End: " << current_time() << endl;
        return result;
    }

    bool operator==(const FlowchartBlock &other) const {
        if (enableLogging) cout << "FlowchartBlock.==: Start: " << current_time() << endl;
        bool result = label == other.label && contents == other.contents;
        if (enableLogging) cout << "FlowchartBlock.==: End: " << current_time() << endl;
        return result;
    }

    [[nodiscard]] size_t size() const {
        return contents.size();
    }

    [[nodiscard]] FlowchartBlock tail() const {
        if (enableLogging) cout << "FlowchartBlock.tail: Start: " << current_time() << endl;
        auto result = contents.size() < 2
                          ? FlowchartBlock(label, {})
                          : FlowchartBlock{label, std::vector(contents.begin() + 1, contents.end())};
        if (enableLogging) cout << "FlowchartBlock.tail: End: " << current_time() << endl;
        return result;
    }

    [[nodiscard]] std::string to_string() const {
        if (enableLogging) cout << "FlowchartBlock.to_string: Start: " << current_time() << endl;
        std::ostringstream oss;
        oss << label << ":\n";
        for (auto &line: contents) {
            oss << "    " << line.to_string() << ";\n";
        }
        if (enableLogging) cout << "FlowchartBlock.to_string: End: " << current_time() << endl;
        return oss.str();
    }
};

class FlowchartProgramState {
    map<string, map<string, string>> label_renaming;

    static string next_label_name() {
        static int counter = 0;
        return "lab" + std::to_string(counter++);
    }

    static string next_tmp_name() {
        static int counter = 0;
        return "tmp%" + std::to_string(counter++);
    }

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
        if (enableLogging) cout << "FlowchartProgramState.split_to_expr: Start: " << current_time() << endl;
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
                if (enableLogging) cout << "FlowchartProgramState.split_to_expr: End: " << current_time() << endl;
                return result;
            }
        }
        if (enableLogging) cout << "FlowchartProgramState.split_to_expr: End: " << current_time() << endl;
        return result;
    }

    string to_string();

    pair<bool, optional<FlowchartValue> > eval_expr(const string &expr, bool is_reduce);
};

class FlowchartList {
public:
    std::vector<optional<FlowchartValue> > values;

    FlowchartList(const std::optional<FlowchartProgramState> &state, bool isReduce, const std::string &s,
                  const optional<vector<optional<FlowchartValue> > > &values);

    FlowchartList(bool isReduce, const std::string &s, const optional<vector<optional<FlowchartValue> > > &values);

    static bool is_correct_string(const std::string &str) {
        return !str.empty() && str.front() == '(' && str.back() == ')';
    }

    [[nodiscard]] optional<FlowchartValue> head() const;

    [[nodiscard]] FlowchartList tail() const;

    void cons(const optional<FlowchartValue> &elem);

    [[nodiscard]] bool is_empty() const;

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
        if (enableLogging) cout << "FlowchartProgram: Start: " << current_time() << endl;
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

        if (enableLogging) cout << "FlowchartProgram: End: " << current_time() << endl;
    }

    static bool is_correct_string(const string &str) {
        if (enableLogging) cout << "FlowchartProgram.is_correct_string: Start: " << current_time() << endl;
        auto lines = vector<string>{};
        for (const auto &raw_line: Util::split_on_level(Util::strip_spaces(str), ';', 0)) {
            auto line = Util::strip_spaces(raw_line);
            if (line.empty()) continue;
            lines.emplace_back(line);
        }
        int i = 0;
        if (lines[0].rfind("read") == 0) {
            for (const auto tokens = Util::split_on_level(lines[0].substr(4), ',', 0); const auto &token: tokens) {
                if (!Util::is_correct_var(Util::strip_spaces(token))) {
                    if (enableLogging) cout << "FlowchartProgram.is_correct_string: End: " << current_time() << endl;
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

            if (!Util::is_correct_label(label)) {
                if (enableLogging) cout << "FlowchartProgram.is_correct_string: End: " << current_time() << endl;
                return false;
            }
            while (!Util::is_correct_jump(line)) {
                if (!Util::is_correct_assignment(line)) {
                    if (enableLogging) cout << "FlowchartProgram.is_correct_string: End: " << current_time() << endl;
                    return false;
                }
                i++;
                line = lines[i];
            }
            i++;
        }
        if (enableLogging) cout << "FlowchartProgram.is_correct_string: End: " << current_time() << endl;
        return true;
    }

    FlowchartProgram parse_program(const bool read_from_input, const optional<FlowchartProgramState> &state) {
        if (enableLogging) cout << "FlowchartProgram.parse_program: Start: " << current_time() << endl;
        auto lines = vector<string>{};
        for (const auto &raw_line: Util::split_on_level(Util::strip_spaces(program), ';', 0)) {
            auto line = Util::strip_spaces(raw_line);
            if (line.empty()) continue;
            lines.emplace_back(line);
        }
        auto result = FlowchartProgram(parent_state, is_reduce, program, "");
        int i = 0;
        if (lines[0].rfind("read") == 0) {
            for (const auto tokens = Util::split_on_level(lines[0].substr(4), ',', 0); const auto &token: tokens) {
                string key = Util::strip_spaces(token);
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
                tokens.emplace_back(Util::strip_spaces(token));
            }
            string label = Util::strip_spaces(tokens[0]);
            string line = Util::join(1, tokens.size(), tokens, ":");

            result.labels.emplace_back(label);
            result.blocks[label] = FlowchartBlock(label, {});
            while (!Util::is_correct_jump(line)) {
                if (line.rfind(" parse ") != string::npos) {
                    auto args = Util::split_on_level(Util::strip_spaces(line), ' ', 0);
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
                    ranges::replace(line_without_spaces, '\n', '_');
                    ranges::replace(line_without_spaces, '\t', '_');
                    ranges::replace(line_without_spaces, ':', '|');
                    ranges::replace(line_without_spaces, ';', '|');
                    const string &after_lookup_label =
                            "after_" + std::to_string(result.lookup_id) + "_" + line_without_spaces;
                    const string &start_lookup_label =
                            "start_" + std::to_string(result.lookup_id) + "_" + line_without_spaces;
                    const string &continue_lookup_label =
                            "continue_" + std::to_string(result.lookup_id) + "_" + line_without_spaces;
                    auto args = Util::split_on_level(Util::strip_spaces(line), ' ', 0);
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
        if (enableLogging) cout << "FlowchartProgram.parse_program: End: " << current_time() << endl;
        return result;
    }

    FlowchartBlock get_block(const string &label) {
        return blocks[label];
    }

    bool has_next(const string &label) {
        if (enableLogging) cout << "FlowchartProgram.has_next: Start: " << current_time() << endl;
        auto result = ranges::find(labels, label) != labels.end();
        if (enableLogging) cout << "FlowchartProgram.has_next: End: " << current_time() << endl;
        return result;
    }

    string get_label(const int index) {
        return labels[index];
    }

    string next_label(const string &label) {
        if (enableLogging) cout << "FlowchartProgram.next_label: Start: " << current_time() << endl;
        auto index = ranges::find(labels, label) - labels.begin() + 1;
        if (index == labels.size()) index--;
        const auto result = labels[index];
        if (enableLogging) cout << "FlowchartProgram.next_label: End: " << current_time() << endl;
        return result;
    }

    [[nodiscard]] std::string to_string() const {
        if (enableLogging) cout << "FlowchartProgram.to_string: Start: " << current_time() << endl;
        std::ostringstream oss;
        for (const auto &label: labels) {
            oss << blocks.at(label).to_string() << "\n";
        }
        if (enableLogging) cout << "FlowchartProgram.to_string: End: " << current_time() << endl;
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
    if (enableLogging) cout << "value_to_string: Start: " << current_time() << endl;
    string result;
    if (value.has_value()) {
        if (auto *v = as<Statement>(value.value())) {
            result = v->to_string();
        } else if (auto *v = as<FlowchartBlock>(value.value())) {
            result = v->to_string();
        } else if (auto *v = as<FlowchartProgram>(value.value())) {
            result = v->to_string();
        } else if (auto *v = as<FlowchartProgramState>(value.value())) {
            result = v->to_string();
        } else if (auto *v = as<FlowchartList>(value.value())) {
            result = v->to_string();
        } else if (auto *v = as<TuringMachineProgram>(value.value())) {
            result = v->to_string();
        } else if (auto *v = as<string>(value.value())) {
            result = *v;
        } else {
            throw std::runtime_error("Unexpected value");
        }
    } else {
        result = "None";
    }

    if (enableLogging) cout << "value_to_string: End: " << current_time() << endl;
    return result;
}

bool FlowchartProgramState::is_static(const FlowchartList &division, const string &expr) {
    if (enableLogging) cout << "FlowchartProgramState.is_static: Start: " << current_time() << endl;
    auto tokens = Util::split_on_level(expr, ' ', 0);
    if (tokens.size() == 1) {
        bool found = false;
        for (const auto &v: division.values) {
            if (value_to_string(v) == tokens[0]) {
                found = true;
                break;
            }
        }
        if (found) {
            if (enableLogging) cout << "FlowchartProgramState.is_static: End: " << current_time() << endl;
            return true;
        }
        if (!tokens[0].empty() && tokens[0][0] == '\'') {
            if (enableLogging) cout << "FlowchartProgramState.is_static: End: " << current_time() << endl;
            return true;
        }
        if (enableLogging) cout << "FlowchartProgramState.is_static: End: " << current_time() << endl;
        return false;
    }

    bool result = ranges::all_of(split_to_expr(vector(tokens.begin() + 1, tokens.end()), Util::functions[tokens[0]]),
                                 [&](const string &s) { return is_static(division, s); });

    if (enableLogging) cout << "FlowchartProgramState.is_static: End: " << current_time() << endl;
    return result;
}

optional<FlowchartValue>
value_from_raw(const string &raw, optional<FlowchartProgramState> state, const bool is_reduce) {
    if (enableLogging) cout << "value_from_raw(" << raw << "): Start: " << current_time() << endl;
    string s = Util::strip_spaces(raw);
    optional<FlowchartValue> result;
    if (s.empty()) result = string("");
    else if (FlowchartList::is_correct_string(s)) result = FlowchartList(state, is_reduce, s, {});
    else if (TuringMachineProgram::is_correct_string(s)) result = TuringMachineProgram(s, {}, {});
    else if (FlowchartProgramState::is_correct_string(s)) result = FlowchartProgramState(state, is_reduce, s);
    else if (FlowchartProgram::is_correct_string(s)) result = FlowchartProgram(state, is_reduce, s, "");
    else if (state.has_value()) result = state.value().eval_expr(s, is_reduce).second;
    else result = s;
    if (enableLogging) cout << "value_from_raw(" << raw << "): End: " << current_time() << endl;
    return result;
}

class FlowchartInterpreter {
    FlowchartProgram program;

    std::optional<std::string> execute_block(const std::string &label) {
        auto block = program.get_block(label);
        size_t i = 0;

        while (i < block.size()) {
            string stmt = block.get_line(i)->to_string();
            if (enableLogging) cout << "stmt: " << stmt << ". Time: " << current_time() << endl;
            auto tokens = Util::split_on_level(block.get_line(i)->to_string(), ' ', 0);
            if (tokens[0] == ":=") {
                std::string expr = Util::join(2, tokens.size(), tokens, " ");
                program.state.variables[tokens[1]] = program.state.eval_expr(expr, false).second;
            } else if (tokens[0] == "goto") {
                return tokens[1];
            } else if (tokens[0] == "if") {
                auto result = program.state.variables[tokens[1]].value();
                return *as<string>(result) == "true" ? tokens[3] : tokens[5];
            } else if (tokens[0] == "return") {
                ofstream ofs("/Users/Timur.Kudashev/CLionProjects/FlowchartFutamura/output.txt");
                ofs << "Returned:" << endl << value_to_string(program.state.variables[tokens[1]]) << endl;
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
            if (label_counter % 1000 == 0) {
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
    if (enableLogging) cout << "FlowchartProgramState: Start: " << current_time() << endl;
    this->variables = {};
    if (!s.empty() && s != "[]") {
        const auto tmp = Util::split_on_level(s.substr(1, s.size() - 2), '$', 0);
        for (int i = 0; i < tmp.size(); i += 2) {
            variables[Util::strip_spaces(tmp[i])] = value_from_raw(Util::strip_spaces(tmp[i + 1]), parent_state, is_reduce);
        }
    }
    if (enableLogging) cout << "FlowchartProgramState: End: " << current_time() << endl;
}

bool FlowchartProgramState::is_empty() const {
    return variables.empty();
}


bool equal_values(const optional<FlowchartValue> &a, const optional<FlowchartValue> &b) {
    if (enableLogging) cout << "equal_values: Start: " << current_time() << endl;
    bool result;
    if (a.has_value() != b.has_value()) result = false;
    else if (!a.has_value()) result = true;
    else if (auto *stmt1 = const_as<Statement>(a.value())) {
        if (auto *stmt2 = const_as<Statement>(b.value())) {
            result = *stmt1 == *stmt2;
        } else result = false;
    } else if (auto *stmt1 = const_as<TuringMachineProgram>(a.value())) {
        if (auto *stmt2 = const_as<TuringMachineProgram>(b.value())) {
            result = *stmt1 == *stmt2;
        } else result = false;
    } else if (auto *stmt1 = const_as<string>(a.value())) {
        if (auto *stmt2 = const_as<string>(b.value())) {
            result = *stmt1 == *stmt2;
        } else result = false;
    } else if (auto *stmt1 = const_as<FlowchartBlock>(a.value())) {
        if (auto *stmt2 = const_as<FlowchartBlock>(b.value())) {
            result = *stmt1 == *stmt2;
        } else result = false;
    } else if (auto *stmt1 = const_as<FlowchartProgramState>(a.value())) {
        if (auto *stmt2 = const_as<FlowchartProgramState>(b.value())) {
            result = *stmt1 == *stmt2;
        } else result = false;
    } else if (auto *stmt1 = const_as<FlowchartProgram>(a.value())) {
        if (auto *stmt2 = const_as<FlowchartProgram>(b.value())) {
            result = stmt1->to_string() == stmt2->to_string();
        } else result = false;
    } else if (auto *stmt1 = const_as<FlowchartList>(a.value())) {
        if (auto *stmt2 = const_as<FlowchartList>(b.value())) {
            result = *stmt1 == *stmt2;
        } else result = false;
    } else {
        throw runtime_error("FlowchartList::equal_values() failed");
    }
    if (enableLogging) cout << "equal_values: End: " << current_time() << endl;
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

void FlowchartProgramState::append(const string &name, const optional<FlowchartValue> &value) {
    variables[name] = value;
}

optional<FlowchartValue> FlowchartProgramState::evaluate(const string &expr) {
    if (enableLogging) cout << "FlowchartProgramState.evaluate: Start: " << current_time() << endl;
    auto result = eval_expr(expr, false).second;
    if (enableLogging) cout << "FlowchartProgramState.evaluate: End: " << current_time() << endl;
    return result;
}

optional<FlowchartValue> FlowchartProgramState::reduce(const string &expr) {
    if (enableLogging) cout << "FlowchartProgramState.reduce: Start: " << current_time() << endl;
    auto result = eval_expr(expr, true).second;
    if (enableLogging) cout << "FlowchartProgramState.reduce: End: " << current_time() << endl;
    return result;
}

FlowchartList::FlowchartList(const std::optional<FlowchartProgramState> &state, bool isReduce, const std::string &s,
                             const optional<vector<optional<FlowchartValue> > > &values) {
    if (enableLogging) cout << "FlowchartList: Start: " << current_time() << endl;
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
    if (enableLogging) cout << "FlowchartList: End: " << current_time() << endl;
}

FlowchartList::FlowchartList(const bool isReduce,
                             const std::string &s,
                             const optional<std::vector<optional<FlowchartValue> > > &values) {
    if (enableLogging) cout << "FlowchartList: Start: " << current_time() << endl;
    if (values.has_value()) {
        this->values = values.value();
    } else if (s == "()" || s.empty()) {
        this->values = {};
    }
    if (enableLogging) cout << "FlowchartList: End: " << current_time() << endl;
}

[[nodiscard]] optional<FlowchartValue> FlowchartList::head() const {
    if (enableLogging) cout << "FlowchartList.head: Start: " << current_time() << endl;
    auto result = values.empty() ? nullopt : optional(values.back());
    if (enableLogging) cout << "FlowchartList.head: End: " << current_time() << endl;
    return result;
}

[[nodiscard]] FlowchartList FlowchartList::tail() const {
    if (enableLogging) cout << "FlowchartList.tail: Start: " << current_time() << endl;
    auto result = values.size() < 2
                      ? FlowchartList(false, "", optional(vector<optional<FlowchartValue> >{}))
                      : FlowchartList(false, "", vector(values.begin(), values.end() - 1));
    if (enableLogging) cout << "FlowchartList.tail: End: " << current_time() << endl;
    return result;
}

void FlowchartList::cons(const optional<FlowchartValue> &elem) {
    if (enableLogging) cout << "FlowchartList.cons: Start: " << current_time() << endl;
    values.emplace_back(elem);
    if (enableLogging) cout << "FlowchartList.cons: End: " << current_time() << endl;
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
    if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): Start: " << current_time() << endl;
    auto tokens = Util::split_on_level(expr, ' ', 0);
    if (tokens.size() == 1) {
        if (variables.contains(tokens[0])) {
            auto result = make_pair(true, variables[tokens[0]]);
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        }
        if (tokens[0][0] == '\'') {
            if (tokens[0].size() == 1 || ranges::find(Util::open_parenthesis, tokens[0][1]) == Util::open_parenthesis.
                end()) {
                auto result = make_pair(true, value_from_raw(tokens[0].substr(1), nullopt, is_reduce));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            auto result = make_pair(true, value_from_raw(tokens[0].substr(1), *this, is_reduce));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        }
        if (is_reduce) {
            auto result = make_pair(false, expr);
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        }
        throw std::runtime_error("Invalid expression");
    }

    if (string op = tokens[0]; Util::functions.contains(op)) {
        const auto args = split_to_expr(vector(tokens.begin() + 1, tokens.end()), Util::functions[op]);
        bool success = true;
        string reduced;
        for (const auto &arg: args) {
            reduced += " ";
            if (!variables.contains(arg)) {
                success = false;
                reduced += arg;
            } else {
                reduced += "'" + value_to_string(variables[arg]);
            }
        }
        if (!success) {
            auto result = make_pair(false, optional(op + reduced));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        }
        if (op == "hd") {
            if (!variables[args[0]].has_value()) {
                auto result = make_pair(true, nullopt);
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }

            if (auto *stmt = as<Statement>(variables[args[0]].value())) {
                auto result = make_pair(true, optional(stmt->head()));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            if (auto *list = as<FlowchartList>(variables[args[0]].value())) {
                auto result = make_pair(true, optional(list->head()));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
        } else if (op == "tl") {
            if (!variables[args[0]].has_value()) {
                auto result = make_pair(true, nullopt);
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }

            if (auto *stmt = as<Statement>(variables[args[0]].value())) {
                auto result = make_pair(true, optional(stmt->tail()));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            if (auto *list = as<FlowchartList>(variables[args[0]].value())) {
                auto result = make_pair(true, optional(list->tail()));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            if (auto *block = as<FlowchartBlock>(variables[args[0]].value())) {
                auto result = make_pair(true, optional(block->tail()));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
        } else if (op == "cons") {
            if (!variables[args[0]].has_value()) {
                auto result = make_pair(true, nullopt);
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }

            if (auto *stmt = as<Statement>(variables[args[1]].value())) {
                stmt->cons(value_to_string(variables[args[0]]));
                auto result = make_pair(true, optional(*stmt));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            if (auto *list = as<FlowchartList>(variables[args[1]].value())) {
                list->cons(variables[args[0]]);
                auto result = make_pair(true, optional(*list));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
        } else if (op == "==") {
            auto result = make_pair(
                true, boolean_to_optional_string(equal_values(variables[args[0]], variables[args[1]])));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "newTail") {
            if (!variables[args[0]].has_value() || !variables[args[1]].has_value()) {
                auto result = make_pair(true, nullopt);
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }

            auto *tm_program = as<TuringMachineProgram>(variables[args[1]].value());
            auto dictionary = tm_program->dictionary;
            auto order = tm_program->order;
            string label = value_to_string(variables[args[0]]);
            int index = 0;
            for (; index < order.size(); index++) {
                if (order[index] == label) break;
            }
            auto new_order = vector(order.begin() + index, order.end());
            map<string, Statement> new_dictionary = {};
            for (const auto &k: new_order) {
                new_dictionary[k] = dictionary[k];
            }
            auto result = make_pair(true, optional(TuringMachineProgram("", new_dictionary, new_order)));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "firstInstruction") {
            if (!variables[args[0]].has_value()) {
                auto result = make_pair(true, nullopt);
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }

            auto *tm_program = as<TuringMachineProgram>(variables[args[0]].value());
            auto dictionary = tm_program->dictionary;
            auto order = tm_program->order;
            auto result = make_pair(true, optional(dictionary[order[0]]));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "firstSym") {
            if (!variables[args[0]].has_value()) {
                auto result = make_pair(true, optional(""));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }

            auto *list = as<FlowchartList>(variables[args[0]].value());
            auto result = make_pair(true, list->head());
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "firstCommand") {
            if (!variables[args[0]].has_value()) {
                auto result = make_pair(true, nullopt);
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }

            auto *block = as<FlowchartBlock>(variables[args[0]].value());
            auto result = make_pair(true, block->get_line(0));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "rest") {
            if (!variables[args[0]].has_value()) {
                auto result = make_pair(true, nullopt);
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }

            auto *tm_program = as<TuringMachineProgram>(variables[args[0]].value());
            auto dictionary = tm_program->dictionary;
            auto order = tm_program->order;
            auto new_order = vector(order.begin() + 1, order.end());
            map<string, Statement> new_dictionary = {};
            for (const auto &k: new_order) {
                new_dictionary[k] = dictionary[k];
            }
            auto result = make_pair(true, optional(TuringMachineProgram("", new_dictionary, new_order)));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "initialCode") {
            string str0 = value_to_string(variables[args[0]]), str1 = value_to_string(variables[args[1]]);
            string label;
            if (label_renaming.contains(str0) && label_renaming[str0].contains(str1)) {
                label = label_renaming[str0][str1];
            } else {
                label = next_label_name();
                label_renaming[str0][str1] = label;
            }
            auto result = make_pair(true, optional(label + ":\n"));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "extendIf") {
            string str2 = value_to_string(variables[args[2]]), str3 = value_to_string(variables[args[3]]), str4 = value_to_string(variables[args[4]]), true_label, false_label;
            if (label_renaming.contains(str2) && label_renaming[str2].contains(str4)) {
                true_label = label_renaming[str2][str4];
            } else {
                true_label = next_label_name();
                label_renaming[str2][str4] = true_label;
            }
            if (label_renaming.contains(str3) && label_renaming[str3].contains(str4)) {
                false_label = label_renaming[str3][str4];
            } else {
                false_label = next_label_name();
                label_renaming[str3][str4] = false_label;
            }
            string code = value_to_string(variables[args[0]]) + "if " + value_to_string(variables[args[1]]) + " goto " + true_label + " else " + false_label + ";\n";
            auto result = make_pair(true, code);
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "extendReturn") {
            string code = value_to_string(variables[args[0]]) + "return " + value_to_string(variables[args[1]])  + ";\n";
            auto result = make_pair(true, code);
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "extendAssignment") {
            auto result = make_pair(true, optional(value_to_string(variables[args[0]]) + ":= " + value_to_string(variables[args[1]]) + " " + value_to_string(variables[args[2]]) + ";\n"));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "extendCode") {
            auto result = make_pair(
                true, optional(value_to_string(variables[args[0]]) + value_to_string(variables[args[1]])));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "eval") {
            auto *program_state = as<FlowchartProgramState>(variables[args[1]].value());
            auto result = make_pair(true, program_state->evaluate(value_to_string(variables[args[0]])));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "reduce") {
            auto *program_state = as<FlowchartProgramState>(variables[args[1]].value());
            auto result = make_pair(true, program_state->reduce(value_to_string(variables[args[0]])));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "addToState") {
            auto *program_state = as<FlowchartProgramState>(variables[args[0]].value());
            program_state->append(value_to_string(variables[args[1]]), variables[args[2]]);
            auto result = make_pair(true, optional(*program_state));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "isStatic") {
            auto result = make_pair(true, boolean_to_optional_string(
                                        is_static(*as<FlowchartList>(variables[args[0]].value()),
                                                  value_to_string(variables[args[1]]))
                                    ));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "lookup") {
            auto *program = as<FlowchartProgram>(variables[args[1]].value());
            auto result = make_pair(true, optional(program->get_block(value_to_string(variables[args[0]]))));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "in") {
            auto *list = as<FlowchartList>(variables[args[1]].value());
            for (optional<FlowchartValue> &v: list->values) {
                if (equal_values(v, variables[args[0]])) {
                    auto result = make_pair(true, boolean_to_optional_string(true));
                    if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " <<
                                       current_time() << endl;
                    return result;
                }
            }
            auto result = make_pair(true, boolean_to_optional_string(false));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "lookupInitial") {
            auto *program = as<FlowchartProgram>(variables[args[0]].value());
            auto result = make_pair(true, optional(program->labels[0]));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "isEmpty") {
            if (!variables[args[0]].has_value()) {
                auto result = make_pair(true, boolean_to_optional_string(true));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            if (auto *block = as<FlowchartBlock>(variables[args[0]].value())) {
                auto result = make_pair(true, boolean_to_optional_string(block->size() == 0));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            if (auto *list = as<FlowchartList>(variables[args[0]].value())) {
                auto result = make_pair(true, boolean_to_optional_string(list->is_empty()));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            if (auto *state = as<FlowchartProgramState>(variables[args[0]].value())) {
                auto result = make_pair(true, boolean_to_optional_string(state->is_empty()));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
        } else if (op == "nextLabel") {
            auto *program = as<FlowchartProgram>(variables[args[1]].value());
            auto result = make_pair(true, program->next_label(value_to_string(variables[args[0]])));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "getLabel") {
            auto *program = as<FlowchartProgram>(variables[args[1]].value());
            auto result = make_pair(true, program->get_label(stoi(value_to_string(variables[args[0]]))));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "hasNext") {
            auto *program = as<FlowchartProgram>(variables[args[1]].value());
            auto result = make_pair(
                true, boolean_to_optional_string(program->has_next(value_to_string(variables[args[0]]))));
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "ternaryOperator") {
            if (value_to_string(variables[args[0]]) == "true") {
                auto result = make_pair(true, variables[args[1]]);
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            auto result = make_pair(true, variables[args[2]]);
            if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                               endl;
            return result;
        } else if (op == "consUniqueIfNotIn") {
            if (variables[args[1]].has_value()) {
                auto *list = as<FlowchartList>(variables[args[1]].value());
                for (auto &v: list->values) {
                    if (equal_values(v, variables[args[0]])) {
                        auto result = make_pair(true, variables[args[1]]);
                        if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " <<
                                           current_time() << endl;
                        return result;
                    }
                }
            }
            if (variables[args[2]].has_value()) {
                auto *list2 = as<FlowchartList>(variables[args[2]].value());
                for (auto &v: list2->values) {
                    if (equal_values(v, variables[args[0]])) {
                        auto result = make_pair(true, variables[args[1]]);
                        if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " <<
                                           current_time() << endl;
                        return result;
                    }
                }
            }
            if (auto *stmt = as<Statement>(variables[args[1]].value())) {
                stmt->cons(value_to_string(variables[args[0]]));
                auto result = make_pair(true, optional(*stmt));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
            if (auto *list = as<FlowchartList>(variables[args[1]].value())) {
                list->cons(variables[args[0]]);
                auto result = make_pair(true, optional(*list));
                if (enableLogging) cout << "FlowchartProgramState.eval_expr(" << expr << "): End: " << current_time() <<
                                   endl;
                return result;
            }
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
