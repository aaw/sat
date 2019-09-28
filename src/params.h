#ifndef __PARAMS_H__
#define __PARAMS_H__

#include <cstdio>
#include <map>
#include <sstream>
#include <string>

#include "types.h"

#define DEFINE_PARAM(param, default_val, help_text)   \
    double PARAM_##param = default_val; \
    ParamRegisterer REG_##param(STRING(param), &PARAM_##param, help_text);

struct Params {
    void register_param(const char* name, double* val, const char* help_text) {
        ptrs[name] = val;
        help[name] = help_text;
    }

    void parse(const std::string& param_defs) {
        std::istringstream iss(param_defs);
        std::string kv;
        while(std::getline(iss, kv, ';')) {
            std::size_t eq = kv.find("=");
            CHECK(eq != std::string::npos)
                << "Error parsing k=v: '" << kv << "'";
            std::string k = kv.substr(0,eq);
            std::string value_str = kv.substr(eq+1);
            double v;
            CHECK(sscanf(value_str.c_str(), "%lf", &v) !=
                  std::char_traits<char>::eof())
                << "Error converting '" << value_str << "' to double.";
            auto itr = ptrs.find(k.c_str());
            CHECK(itr != ptrs.end())
                << "Attempt to set undefined parameter '" << k << "'";
            PRINT << "c Overriding param: " << k << " = " << v << std::endl;
            *itr->second = v;
        }
    }

    bool empty() {
        return ptrs.empty();
    }

    std::string help_string() {
        static const int kLineLength = 80;
        static const int kMaxHelpTextLength = 2048;
        static const char kIndent[] = "     ";
        char ht[kMaxHelpTextLength];
        std::ostringstream oss;
        for (const auto& kv : help) {
            size_t last_break = (size_t)oss.tellp();
            oss << kIndent << kv.first << ": ";
            strcpy(ht, kv.second);
            for(char* sp = strtok(ht, " "); sp != NULL;) {
                size_t chars_in_line = (size_t)oss.tellp() - last_break;
                if (chars_in_line % kLineLength >
                    (chars_in_line + strlen(sp) + 1) % kLineLength) {
                    oss << std::endl;
                    last_break = (size_t)oss.tellp();
                    oss << kIndent << "  ";
                    for (size_t i = 0; i < strlen(kv.first); ++i) oss << " ";
                }
                oss << sp << " ";
                sp = strtok(NULL, " ");
            }
            oss << std::endl << kIndent << "  ";
            for (size_t i = 0; i < strlen(kv.first); ++i) oss << " ";
            oss << "Default: " << *ptrs[kv.first] << std::endl << std::endl;
        }
        return oss.str();
    }

    static Params& singleton() {
        static Params s;
        return s;
    }
private:
    std::map<const char*, double*, cstrcmp> ptrs;
    std::map<const char*, const char*, cstrcmp> help;
};

struct ParamRegisterer {
    ParamRegisterer(const char* name, double* value, const char* help_text) {
        Params::singleton().register_param(name, value, help_text);
    }
};

#endif  // __PARAMS_H__
