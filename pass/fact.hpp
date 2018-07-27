#ifndef FACT_HPP
#define FACT_HPP

/*
 * base fact class
 */
class Fact {
public:
	enum Op {
		Mov,
		FConst, IConst,
		IAnd32, IXor32, FAdd32, FAbs32, FOlt32, CopySign32,
		IAnd64, IXor64, FAdd64, FAbs64, FOlt64, CopySign64,
		Sel
	};

	std::vector<llvm::Value *> vars;
	std::vector<Range> ranges;

	Op op;
	std::vector<Fact *> args;

	Fact() { };
	Fact(Op opv) { op = opv; }
	Fact(Op opv, Range init) { op = opv; ranges.push_back(init); }
	Fact(Op opv, Range64 init) { op = opv; ranges.push_back(Range(init)); }
	~Fact() {}

	double Lower() const;
	double Upper() const;
	std::string Str() const;
	void Dump() const;

	void InvProp();

	static Fact FltAdd64(Fact &lhs, Fact &rhs);
	static Fact FltAbs64(Fact &in);
	static Fact FltOLT64(Fact &lhs, Fact &rhs, llvm::Value *var);
	static Fact FltCopySign64(Fact &lhs, Fact &rhs);
	static Fact IntAnd64(Fact &lhs, Fact &rhs);
	static Fact IntXor64(Fact &lhs, Fact &rhs);

	static Fact Select(Fact &cond, Fact &lhs, Fact &rhs, llvm::Value *var);

	static double Next64(double val) { return std::nextafter(val, INFINITY); }
	static double Prev64(double val) { return std::nextafter(val, -INFINITY); }

	uint64_t Limit() const;
	int32_t Index(const llvm::Value *var) const;
	Range &Map(const std::vector<llvm::Value *> &vars, uint64_t idx);

	static std::vector<llvm::Value *> Cross(const std::vector<llvm::Value *> &lhs, const std::vector<llvm::Value *> &rhs);
};


/*
 * pass class
 */
class Pass {
public:
	llvm::Function *func;
	std::map<llvm::Value *, Fact> map;

	Pass() = delete;
	Pass(llvm::Function *init) { func = init; }
	~Pass() {}

	void Run();
	void Add(llvm::Value *value, const Fact &fact);

	Fact &Get(llvm::Value *value);
	std::pair<Fact::Op, std::vector<Fact *>> Info(llvm::Instruction &inst);

	void Dump() const;
};

#endif
