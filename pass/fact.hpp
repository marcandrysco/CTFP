#ifndef FACT_HPP
#define FACT_HPP

/*
 * class prototypes
 */
class Fact;
class IvalF64;
class IvalI64;
class Pass;
class RangeF64;

/*
 * operation type enumerator
 */
enum class Op {
	None,
	CastI64toF64, CastF64toI64,
	ConstF32, ConstI32, Mov32, AbsF32, CopySignF32, AddF32, SubF32, MulF32, CmpOltF32, CmpOgtF32,
	ConstF64, ConstI64, Mov64, AbsF64, CopySignF64, AddF64, SubF64, MulF64, CmpOltF64, CmpOgtF64,
	SelectI32, AndI32, XorI32,
	SelectI64, AndI64, XorI64,
};

/*
 * pass class
 */
class Pass {
public:
	std::map<const llvm::Value *, Fact> map;

	Pass() { }
	~Pass() { }

	void Run(const llvm::Function &func, std::vector<Range> const &args);
	void Inst(const llvm::Instruction &inst);
	void Dump(const llvm::Function &func) const;

	Fact& Get(llvm::Value *value);
	std::pair<Op, std::vector<Fact *>> Info(const llvm::Instruction &inst);
};

/*
 * fact class
 */
class Fact {
public:
	Op op;
	std::vector<Fact *> args;

	std::vector<const llvm::Value *> vars;
	std::vector<Range> ranges;

	Fact() { op = Op::None; ranges.push_back(Range(RangeNone())); }
	Fact(Op _op, std::vector<Fact *> _args) { op = _op; args = _args; }
	Fact(Op _op, std::vector<Fact *> _args, const llvm::Value *_var) { op = _op; args = _args; vars = std::vector<const llvm::Value *>{ _var }; }
	Fact(Op _op, std::vector<Fact *> _args, std::vector<const llvm::Value *> const &_vars) { op = _op; args = _args; vars = _vars; }
	Fact(Op _op, std::vector<Fact *> _args, Range _range) { op = _op; args = _args; ranges.push_back(_range); }
	Fact(Op _op, std::vector<Fact *> _args, RangeBool _range) { op = _op; args = _args; ranges.push_back(Range(_range)); }
	Fact(Op _op, std::vector<Fact *> _args, RangeF64 _range) { op = _op; args = _args; ranges.push_back(Range(_range)); }
	Fact(Op _op, std::vector<Fact *> _args, RangeI64 _range) { op = _op; args = _args; ranges.push_back(Range(_range)); }
	~Fact() { }

	void InvProp();
	double LowerF64() const;
	double UpperF64() const;

	uint64_t Limit() const;
	int32_t Index(const llvm::Value *var) const;
	Range &Map(const std::vector<const llvm::Value *> &vars, uint64_t idx);

	std::string Str() const;
	void Dump() const;

	static Fact AbsF64(Fact &in);
	static Fact AddF64(Fact &lhs, Fact &rhs, const llvm::Value *var);
	static Fact SubF64(Fact &lhs, Fact &rhs, const llvm::Value *var);
	static Fact MulF64(Fact &lhs, Fact &rhs, const llvm::Value *var);
	static Fact CmpOltF64(Fact &lhs, Fact &rhs, const llvm::Value *var);
	static Fact CmpOgtF64(Fact &lhs, Fact &rhs, const llvm::Value *var);
	static Fact CopySignF64(Fact &mag, Fact &sign);
	static Fact AndI64(Fact &lhs, Fact &rhs);
	static Fact XorI64(Fact &lhs, Fact &rhs);
	static Fact SelectI64(Fact &cond, Fact &ontrue, Fact &onfalse);
	static Fact CastF64toI64(Fact &in);
	static Fact CastI64toF64(Fact &in);

	static std::vector<const llvm::Value *> Cross(std::vector<const llvm::Value *> const &lhs, std::vector<const llvm::Value *> const &rhs);

	static double Next64(double val) { return std::nextafter(val, INFINITY); }
	static double Prev64(double val) { return std::nextafter(val, -INFINITY); }
};

#endif
