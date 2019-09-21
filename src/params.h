#ifndef __PARAMS_H__
#define __PARAMS_H__

#include <cstdio>
#include <map>
#include <sstream>
#include <string>

#include "types.h"

#define DEFINE_PARAM(param, default_val, help_text)   \
    double PARAM_##param = default_val; \
    ParamRegisterer REG_##param(STRING(param), &PARAM_##param);

struct Params {
    void register_param(const char* name, double* val) {
        ptrs[name] = val;
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

    // TODO: store help_text, dump a help string.

    static Params& singleton() {
        static Params s;
        return s;
    }
private:
    std::map<const char*, double*, cstrcmp> ptrs;
};

struct ParamRegisterer {
    ParamRegisterer(const char* name, double* value) {
        Params::singleton().register_param(name, value);
    }
};

#endif  // __PARAMS_H__
