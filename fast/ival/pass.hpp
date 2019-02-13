#pragma once

/*
 * Pass class
 */
class Pass {
public:
	Pass() { }
	~Pass() { }

	std::map<const llvm::Value *, Range> map;

	/**
	 * Given a value, retrieve the associated fact.
	 *   @value: The value.
	 *   &returns: The fact.
	 */
	Range& GetRange(llvm::Value *value) {
		auto find = map.find(value);
		if(find != map.end())
			return find->second;

		if(llvm::isa<llvm::UndefValue>(value)) {
			Type type = GetType(*value);

			switch(type.kind) {
			case Kind::Flt:
				if(type.width == 32)
					return map[value] = Range(RangeVecF32::Undef(type.count));
				else if(type.width == 64)
					return map[value] = Range(RangeVecF64::Undef(type.count));
				else
					return map[value] = Range();

			default:
				return map[value] = Range();
			}
		}
		else if(llvm::isa<llvm::ConstantFP>(value)) {
			llvm::ConstantFP *fp = llvm::cast<llvm::ConstantFP>(value);

			if(value->getType()->isFloatTy())
				map[value] = Range::ConstF32(fp->getValueAPF().convertToFloat());
			else if(value->getType()->isDoubleTy())
				map[value] = Range::ConstF64(fp->getValueAPF().convertToDouble());
			else
				map[value] = Range();

			return map[value];
		}
		else if(llvm::isa<llvm::ConstantInt>(value)) {
			llvm::ConstantInt *ival = llvm::cast<llvm::ConstantInt>(value);

			if(value->getType()->isIntegerTy(32))
				map[value] = Range::ConstI32(ival->getZExtValue());
			else if(value->getType()->isIntegerTy(64))
				map[value] = Range::ConstI64(ival->getZExtValue());
			else
				map[value] = Range();

			return map[value];
		}
		else if(llvm::isa<llvm::ConstantDataVector>(value)) {
			llvm::ConstantDataVector *vec = llvm::cast<llvm::ConstantDataVector>(value);
			uint32_t i, n = vec->getNumElements();

			if(vec->getType()->getElementType()->isIntegerTy(32)) {
				RangeVecI32 range;

				for(i = 0; i < n; i++)
					range.scalars.push_back(RangeI32::Const(vec->getElementAsInteger(i)));

				return map[value] = Range(range);
			}
			else if(vec->getType()->getElementType()->isIntegerTy(64)) {
				RangeVecI64 range;

				for(i = 0; i < n; i++)
					range.scalars.push_back(RangeI64::Const(vec->getElementAsInteger(i)));

				return map[value] = Range(range);
			}
			else if(vec->getType()->getElementType()->isFloatTy()) {
				RangeVecF32 range;

				for(i = 0; i < n; i++)
					range.scalars.push_back(RangeF32::Const(vec->getElementAsFloat(i)));

				return map[value] = Range(range);
			}
			else if(vec->getType()->getElementType()->isDoubleTy()) {
				RangeVecF64 range;

				for(i = 0; i < n; i++)
					range.scalars.push_back(RangeF64::Const(vec->getElementAsDouble(i)));

				return map[value] = Range(range);
			}
			else
				return map[value] = Range();
		}
		else if(llvm::isa<llvm::ConstantVector>(value)) {
			llvm::ConstantVector *vec = llvm::cast<llvm::ConstantVector>(value);
			uint32_t i, n = vec->getType()->getNumElements();

			if(vec->getType()->getElementType()->isFloatTy()) {
				RangeVecF32 range;

				for(i = 0; i < n; i++) {
					llvm::Constant *c = vec->getAggregateElement(i);

					if(llvm::isa<llvm::ConstantFP>(c))
						range.scalars.push_back(RangeF32::Const(llvm::cast<llvm::ConstantFP>(c)->getValueAPF().convertToFloat()));
					else if(llvm::isa<llvm::UndefValue>(c))
						range.scalars.push_back(RangeF32::Undef());
					else
						range.scalars.push_back(RangeF32::All());
				}

				return map[value] = Range(range);
			}
			else if(vec->getType()->getElementType()->isDoubleTy()) {
				RangeVecF64 range;

				for(i = 0; i < n; i++) {
					llvm::Constant *c = vec->getAggregateElement(i);

					if(llvm::isa<llvm::ConstantFP>(c))
						range.scalars.push_back(RangeF64::Const(llvm::cast<llvm::ConstantFP>(c)->getValueAPF().convertToDouble()));
					else if(llvm::isa<llvm::UndefValue>(c))
						range.scalars.push_back(RangeF64::Undef());
					else
						range.scalars.push_back(RangeF64::All());
				}

				return map[value] = Range(range);
			}
			else
				return map[value] = Range();
		}
		else if(llvm::isa<llvm::ConstantAggregateZero>(value)) {
			llvm::ConstantAggregateZero *zero = llvm::cast<llvm::ConstantAggregateZero>(value);

			if(zero->getType()->isVectorTy()) {
				if(zero->getType()->getVectorElementType()->isIntegerTy(32))
					return map[value] = Range(RangeVecI32::Const(0, zero->getType()->getVectorNumElements()));
				else if(zero->getType()->getVectorElementType()->isIntegerTy(64))
					return map[value] = Range(RangeVecI64::Const(0, zero->getType()->getVectorNumElements()));
				else if(zero->getType()->getVectorElementType()->isFloatTy())
					return map[value] = Range(RangeVecF32::Const(0.0, zero->getType()->getVectorNumElements()));
				else if(zero->getType()->getVectorElementType()->isDoubleTy())
					return map[value] = Range(RangeVecF64::Const(0.0, zero->getType()->getVectorNumElements()));
				else
					return map[value] = Range();
			}
			else
				return map[value] = Range();
		}
		else
			return map[value] = Range();
	}

	/**
	 * Process an instruction.
	 *   @inst: The instruction.
	 */
	void Proc(llvm::Instruction const &inst) {
		Range *lhs, *rhs;
		Info info = GetInfo(inst);

		switch(info.op) {
		case Op::Add:
			lhs = &GetRange(inst.getOperand(0));
			rhs = &GetRange(inst.getOperand(1));
			map[&inst] = Range::Add(*lhs, *rhs, info.type);
			break;

		case Op::Sub:
			lhs = &GetRange(inst.getOperand(0));
			rhs = &GetRange(inst.getOperand(1));
			map[&inst] = Range::Sub(*lhs, *rhs, info.type);
			break;

		case Op::Mul:
			lhs = &GetRange(inst.getOperand(0));
			rhs = &GetRange(inst.getOperand(1));
			map[&inst] = Range::Mul(*lhs, *rhs, info.type);
			break;

		case Op::Div:
			lhs = &GetRange(inst.getOperand(0));
			rhs = &GetRange(inst.getOperand(1));
			map[&inst] = Range::Div(*lhs, *rhs, info.type);
			break;

		case Op::And:
			map[&inst] = Range::And(GetRange(inst.getOperand(0)), GetRange(inst.getOperand(1)), info.type);
			break;

		case Op::Or:
			map[&inst] = Range::Or(GetRange(inst.getOperand(0)), GetRange(inst.getOperand(1)), info.type);
			break;

		case Op::Xor:
			map[&inst] = Range::Xor(GetRange(inst.getOperand(0)), GetRange(inst.getOperand(1)), info.type);
			break;

		case Op::CmpOLT:
			map[&inst] = Range::CmpOLT(GetRange(inst.getOperand(0)), GetRange(inst.getOperand(1)), info.type);
			break;

		case Op::CmpOGT:
			map[&inst] = Range::CmpOGT(GetRange(inst.getOperand(0)), GetRange(inst.getOperand(1)), info.type);
			break;

		case Op::Select:
			map[&inst] = Range::Select(GetRange(inst.getOperand(0)), GetRange(inst.getOperand(1)), GetRange(inst.getOperand(2)), info.type);
			break;

		case Op::Abs:
			map[&inst] = Range::Abs(GetRange(inst.getOperand(0)), info.type);
			break;

		case Op::ItoF:
			//in = &GetRange(inst.getOperand(0));
			//map[&inst] = Range::ItoF(*in, info.type);
			break;

		case Op::FtoI:
			//in = &GetRange(inst.getOperand(0));
			//map[&inst] = Range::FtoI(*in, info.type);
			break;

		case Op::Insert:
			if(llvm::isa<llvm::ConstantInt>(inst.getOperand(2))) {
				int32_t idx = llvm::cast<llvm::ConstantInt>(inst.getOperand(2))->getZExtValue();

				Range vec = GetRange(inst.getOperand(0));
				Range val = GetRange(inst.getOperand(1));

				if(std::holds_alternative<RangeVecF32>(vec.var)) {
					if(std::holds_alternative<RangeVecF32>(val.var)) {
						RangeVecF32 range = std::get<RangeVecF32>(vec.var);
						range.scalars[idx] = std::get<RangeVecF32>(val.var).scalars[0];
						map[&inst] = range;
					}
					else
						map[&inst] = Range();
				}
				else if(std::holds_alternative<RangeVecF64>(vec.var)) {
					if(std::holds_alternative<RangeVecF64>(val.var)) {
						RangeVecF64 range = std::get<RangeVecF64>(vec.var);
						range.scalars[idx] = std::get<RangeVecF64>(val.var).scalars[0];
						map[&inst] = range;
					}
					else
						map[&inst] = Range();
				}
				else
					map[&inst] = Range();
			}
			else
				map[&inst] = Range();
			
			break;

		default:
			break;
		}
	}

	/**
	 * Dump the set of facts from a function.
	 */
	void Dump(llvm::Function const& func) const {
		for(auto &block : func) {
			std::cout << block.getName().data() << ":\n";

			for(auto &inst : block) {
				inst.print(llvm::outs());
				std::cout << "\n";

				auto fact = map.find(&inst);
				if(fact != map.end())
					printf("    %s\n", fact->second.Str().data());
				else
					printf("    missing\n");
			}
		}
	}


	/**
	 * Retrieve the type for a value.
	 *   @inst: The instruction.
	 *   &returns: The operation.
	 */
	static Type GetType(llvm::Value const& val) {
		if(val.getType()->isFloatTy())
			return Type(Kind::Flt, 32);
		else if(val.getType()->isDoubleTy())
			return Type(Kind::Flt, 64);
		else if(val.getType()->isVectorTy()) {
			uint32_t cnt = val.getType()->getVectorNumElements();

			if(val.getType()->getScalarType()->isFloatTy())
				return Type(Kind::Flt, 32, cnt);
			else if(val.getType()->getScalarType()->isDoubleTy())
				return Type(Kind::Flt, 64, cnt);
			else
				return Type();
		}
		else
			return Type();
	}

	/**
	 * Retrieve the operation for an instruction.
	 *   @inst: The instruction.
	 *   &returns: The operation.
	 */
	static Op GetOp(llvm::Instruction const& inst) {
		switch(inst.getOpcode()) {
		case llvm::Instruction::FAdd:
			return Op::Add;

		case llvm::Instruction::FSub:
			return Op::Sub;

		case llvm::Instruction::FMul:
			return Op::Mul;

		case llvm::Instruction::FDiv:
			return Op::Div;

		case llvm::Instruction::And:
			return Op::And;

		case llvm::Instruction::Or:
			return Op::Or;

		case llvm::Instruction::Xor:
			return Op::Xor;

		case llvm::Instruction::Select:
			return Op::Select;

		case llvm::Instruction::BitCast:
			if(inst.getType()->isIntegerTy(64) && inst.getOperand(0)->getType()->isDoubleTy())
				return Op::FtoI;
			else if(inst.getType()->isDoubleTy() && inst.getOperand(0)->getType()->isIntegerTy(64))
				return Op::ItoF;
			else
				return Op::Unk;

		case llvm::Instruction::FCmp:
			switch(llvm::cast<llvm::FCmpInst>(&inst)->getPredicate()) {
			case llvm::CmpInst::FCMP_OLT: return Op::CmpOLT; break;
			case llvm::CmpInst::FCMP_OGT: return Op::CmpOGT; break;
			case llvm::CmpInst::FCMP_OEQ: return Op::CmpOEQ; break;
			default: return Op::Unk;
			}

		case llvm::Instruction::InsertElement:
			return Op::Insert;

		case llvm::Instruction::ExtractElement:
			return Op::Extract;

		case llvm::Instruction::Call:
			{
				const llvm::CallInst *call = llvm::cast<llvm::CallInst>(&inst);

				if(call->getCalledFunction() == nullptr)
					return Op::Unk;

				if(call->getCalledFunction()->getName().startswith("llvm.fabs."))
					return Op::Abs;
				else if(call->getCalledFunction()->getName().startswith("llvm.sqrt."))
					return Op::Sqrt;
				else
					return Op::Unk;
			}
			break;

		default:
			return Op::Unk;
		}
	}

	/**
	 * Retrieve the operation info for an instruction.
	 *   @inst: The instruction.
	 *   &returns: The info.
	 */
	static Info GetInfo(llvm::Instruction const& inst) {
		Op op = GetOp(inst);

		if((inst.getOpcode() == llvm::Instruction::ICmp) || (inst.getOpcode() == llvm::Instruction::FCmp))
			return Info(op, GetType(*inst.getOperand(0)));
		else if(inst.getOpcode() == llvm::Instruction::Select)
			return Info(op, GetType(*inst.getOperand(1)));
		else if(op != Op::Unk)
			return Info(op, GetType(inst));
		else
			return Info(op, Type());
	}
};
