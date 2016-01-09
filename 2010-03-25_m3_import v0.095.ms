------------------------------------------------------------------------------------------------
-- Starcraft 2 Model (M3->3ds) Importer version 0.095
-- by NiNtoxicated (madyavic@gmail.com)
-- Imports M3 files into 3ds max via maxscript
-- Created for 3ds max 2010, but should be backwards compatible
-- Based on reworked code from my World of Warcraft M2 importer
--
-- Big thanks to Teal (starcraft.incgamers.com) and 
-- Volcore (http://volcore.limbicsoft.com/) for help figuring out the M3 format
--
-- If you use any of this code in your own scripts, please credit
-- where it is due.
--
-- Things to do:
-- 1. Clean up messy code
-- 2. Implement 3dsMax GUI
-- 3. Automate MPQ extraction
-- 4. Add good animation support
--
------------------------------------------------------------------------------------------------

-- Version History:
-- 0.095 -- March 21st 2010
-- Some basic error catching added
-- Fixed initial bone errors
--
-- 0.09 -- March 20th 2010
-- Added primitive animation support
-- Code housekeeping
-- Updated code, improved processing time
--
-- 0.06 -- March 13th 2010
-- Added rollout menu
--
-- 0.05 -- March 11th 2010
-- Added bone support, however mesh not binding to bones properly yet
--
-- 0.04 -- March 6th 2010
-- Major overhaul of code
-- Reworked tag reading and reference reading, can now read nested structures
-- Vastly improved material reading
--
-- 0.03 -- March 4th 2010
-- Vertice normals added 
-- Added material importing
--
-- 0.02 -- February 29th 2010 - March 2nd 2010
-- Made significant improvements to structures and accessing file data
-- Can now (hopefully) import UV data
-- Added submesh functionality
--
-- 0.01 -- February 26th 2010
-- Initial version of M3 import script
--


-- globals
global head, cmat, mread, aread, bstream, cbones
global scrStart, scrEnd -- For script timeStamps
global tread		= #()
global cmesh		= #()

-- Switches
global flipuv_y 				= true
global doCreateBones 		= false --#warning: can slow import
global doTransformBones 	= true
global doCreateSkin 		= true
global doCreateMesh 		= true

-- Misc. variables
global bonesize 	= 0.025
global g_animid 	= 2
global useFPS 	= 30

--Function declaration
fn ReadTagData tagInd flags = ()

-- *******************
--  M3 STRUCTURES
-- ******************* 
struct M3_Header
(
	fileID, ofsTag, nTag, modlref
)

struct M3_Ref
(
	entries, refid, data = #()
)

struct M3_MODL
(
	name,  -- max model name
	versID, 
	SEQS, STC, STS, STG, -- anim info
	bones, 
	vflags, verts, DIV, blist,
    extents,
	matm, mat
)

struct M3_Tag -- Tag data
(
	dataID, ofsData, nData, flags
)

struct M3_AnimData
(
	name, maxframes
)

struct M3_Animoffs 
(
	ind, flags
)

struct M3_AnimBlock -- Sequence Data
(
	frames, flags, fend, keys
)

struct M3_SequenceData --Animation Sequence Header
(
	name, animid, animref, animoffs, trans, rot, scale
)

struct M3_Vertex
(
	pos = #(), bw = #(), bi = #(), normal = #(), uv = [0,0,0]
)

struct M3_DIV -- Model divisions
(
	faces, smeshes, bat, msec
)

struct M3_Sref -- Submesh refrences
(
	subid, matid
)

struct M3_Submesh
(
	indverts, nverts, indfaces, nfaces
)

struct M3_MATM
(
	matind, matref
)

struct M3_Mat
(
	name, layrs
)

struct M3_Mat_Layr
(
	diff, spec, emis, norm
)

struct M3_Layr --more work to be done at a later point
(
	name
)

struct M3_Bone
(
	name, parent, pos, transid, rotid, rot, scale
)

-- ***********
--  HELPERS
-- ***********
-- Liberally stolen from my M2 script
fn echo msg =
(
	format "%\n" (msg) to:listener
)

fn ReadFixedString fixedLen=
(
	local str = ""
	for i = 1 to fixedLen do
	(
		str += bit.intAsChar (ReadByte bstream #unsigned)
	)
	return str
)

fn ReadVec flag array:0 =
(
	local va = #()
	local vec = [0,0,0]
	if array == 0 then count = 1 else count = array
	for i = 1 to count do
	(
		case flag of
		(
			#v3dshort: (vec.x = ReadShort bstream #unsigned; vec.y = ReadShort bstream #unsigned; vec.z = ReadShort bstream #unsigned;)
			#v3dlong: (vec.x = ReadLong bstream #unsigned; vec.y = ReadLong bstream #unsigned; vec.z = ReadLong bstream #unsigned;)
			#v3dbyte: (vec.x = ReadByte bstream #unsigned; vec.y = ReadByte bstream #unsigned; vec.z = ReadByte bstream #unsigned;)
			#quat: (vec = quat 0 0 0 1; vec.x = ReadFloat bstream; vec.y = ReadFloat bstream; vec.z = ReadFloat bstream; vec.w = ReadFloat bstream;)
			#v4dshort: (vec = [0,0,0,0]; vec.x = ReadShort bstream #signed; vec.y = ReadShort bstream #signed; vec.z = ReadShort bstream #signed; vec.w = ReadShort bstream #signed;)
			#v4dbyte: (vec = [0,0,0,0]; vec.x = ReadByte bstream; vec.y = ReadByte bstream; vec.z = ReadByte bstream; vec.w = ReadByte bstream;)
			#v3d: (vec = [0.0,0.0,0.0]; vec.x = ReadFloat bstream; vec.y = ReadFloat bstream; vec.z = ReadFloat bstream;)
		)
		if (array != 0) then (append va vec) else (va = vec)
	)
	
	return va
)

fn SkipBytes count=
(
	local unknown
	case count of
	(
		2: unknown = ReadShort bstream #unsigned
		4: unknown = ReadLong bstream #unsigned
		default:
		(
			for i = 1 to count do
			(
				unknown = ReadByte bstream #unsigned
			)
		)
	)
)
	
fn LongToString num=
(
	local str = ""
	for i = 1 to 4 do
	(
		str += bit.intAsChar (bit.and num 0xff)
		-- num = bit.shift num -8
		num /= 256
	)
	str
)

fn ShortToFloat &val = -- Short to Float func
(
	if (val > 0) then (val -= 32767) else (val += 32767)
	val /= 32767.0
)

fn M3_Convert_Time t =
(
	t / (1000 / useFPS)
)

fn M3_Reset_Globals =
(
	head = cmat = mread = aread = bstream = cbones = cmesh = tread = undefined
	gc()
)

-- ************************
-- M3 FUNCTIONS
-- ************************ 
fn M3_Open fname =
(
	M3_Reset_Globals()
	
	step = "Accessing Model File"
	
	bstream = fopen fname "rb"
	if bstream==undefined then 
	(
		echo "File not found!"
		throw "File not found"
	)
)

fn M3_Close =
(
	step = "Close"
	fclose bstream
	M3_Reset_Globals()
	
	scrEnd = TimeStamp()
	format "Importing took % seconds\n" ((scrEnd - scrStart) / 1000.0)
)

fn ReadRef flags:0 =
(	
	local r = M3_Ref()
	r.entries 	= ReadLong bstream #unsigned
	r.refid		= ReadLong bstream #unsigned + 1
	r.data 		= ReadTagData r.refid flags
	
	return r.data
)

fn M3_Read_Tags =
(
	step = "Read Tags"
	local tr = #()
	if (fseek bstream head.ofsTag #seek_set ) then
	(	
		for i=1 to head.nTag  do
		(
			local t 		= M3_Tag()
			t.dataID 	= ReadFixedString 4
			t.ofsData	= ReadLong bstream #unsigned
			t.nData		= ReadLong bstream #unsigned
			t.flags		= ReadLong bstream #unsigned
		
			append tr t
		)
	)
	
	return tr
)

fn M3_Read_Header =
(
	head = M3_Header()
	if head == undefined or bstream == undefined then
		echo "Nothing to read"

	format "Reading Model Header...\n" to:listener
	step = "Read header"
	head.fileID = (ReadFixedString 4)
	echo ("Filetype: "+(head.fileID))
	if (head.fileID != "33DM") then
	(
		echo "Not a valid Starcraft 2 model file!"
		throw "Not a valid Starcraft model file!"
	)
	else
	(
		head.ofsTag 	= ReadLong bstream #unsigned
		head.nTag		= ReadLong bstream #unsigned
		
		local bm = ftell(bstream) -- bookmark
		tread = M3_Read_Tags() -- collect for future parsing
		fseek bstream bm #seek_set -- return to bookmark
		echo "---- Header finished ----\n"
	)
)

fn M3_Read_Start =
(
	step = "Read Model Data"
	scrStart = TimeStamp() -- start tracking script processing time
	mread = ReadRef()
)

fn M3_Name name flt ext:undefined =
(
	-- Filter name from path
	local mn = filterString name flt
	mn = mn[mn.count]
	local mext = substring mn (mn.count-3) (4)
	if (ext != undefined) then
	(
		if (matchPattern mext pattern:ext ignoreCase:true) then mn = substring mn 1 (mn.count-4)
	)
	return mn
)

fn M3_Read_MODL td =
(
	m 					= M3_MODL()
	local mname 	= ReadRef()
	m.name 			= M3_Name mname "\\" ext:".max"
	echo ("Model Name: " + m.name)	
	m.versID 		= ReadLong bstream #unsigned
	-- Don't read in unneccessary big chunks of data unless transforming bones
	if (doCreateBones and doTransformBones) then 
	(
		m.SEQS	= ReadRef()
		aread = ReadRef()
		echo "Animations read\n"
	)
	else
	(
		SkipBytes 16
	)
	SkipBytes 28
	echo "Reading bones..."
	m.bones			= ReadRef()
	echo "Bones read\n"
	SkipBytes 4
	echo "Reading mesh data..."
	m.vflags			= ReadLong bstream #unsigned
	m.verts			= ReadRef flags:m.vflags
	m.DIV			= ReadRef()
	m.blist			= ReadRef flags:#ushort
	echo "Mesh data read\n"
	if td.flags != 20  then SkipBytes 128 else SkipBytes 120
	echo "Reading materials..."
	m.matm			= ReadRef()
	m.mat			= ReadRef()
	echo "Materials read\n"
	
	return m
)

fn M3_Read_AnimData td =
(
	ad = #()
	for i = 1 to td.nData do
	(
		a = M3_AnimData()
		
		SkipBytes 8
		a.name = ReadRef()
		SkipBytes 4
		local mframes = ReadLong bstream #unsigned
		a.maxframes = M3_Convert_Time mframes
		SkipBytes 64
		
		append ad a
	)
	
	echo ("nAnims: " + ad.count as string)
	return ad
)

fn M3_Read_AnimBlock td =
(
	ac = #()
	
	for i = 1 to td.nData do
	(
		ab = M3_AnimBlock()
		ab.frames = ReadRef flags:#ulong
		ab.flags = ReadLong bstream #unsigned
		ab.fend	= ReadLong bstream #unsigned
		ab.keys = ReadRef()
		
		append ac ab
	)
	
	return ac
)

fn M3_Read_SequenceData td =
(
	ac = #()
	for i = 1 to td.nData do
	(
		a = M3_SequenceData()

		a.name 		= ReadRef()
		SkipBytes 8
		a.animid		= ReadRef flags:#ulong
		a.animoffs	= ReadRef flags:#animind
		SkipBytes 20
		a.trans		= ReadRef()
		a.rot			= ReadRef()
		SkipBytes 72
		
		append ac a
	)
	
	return ac
)

fn M3_Read_Bones td =
(
	step = "Read Bones"
	
	br = #()
	
	for i = 1 to td.nData do
	(
		local b = M3_Bone()
		SkipBytes 4
		b.name = ReadRef()
		--echo ("Bone_" + i as string + ": " + b.name)
		SkipBytes 4
		b.parent = ReadShort bstream #signed + 1
		SkipBytes 6
		b.transid = ReadLong bstream #unsigned
		b.pos = ReadVec #v3d
		SkipBytes 20
		b.rotid = ReadLong bstream #unsigned
		b.rot = ReadVec #quat
		SkipBytes 28
		b.scale = ReadVec #v3d
		SkipBytes 36
			
		append br b
	)
	echo ("nBones: "+br.count as string)
	
	return br
)

fn M3_Read_Verts td flags =
(
	step = "Read Verts"
	
	local vr = #()
	local vsize, bsize; --vertice/buffer size, many thanks to Volcore for discovering these flags and their meanings!
	if ((bit.and flags 0x40000) == 0) then
	(
		vsize = 32
		bsize = 4
	)
	else
	(
		vsize = 36
		bsize = 8
	)
	
	for i=1 to (td.nData/vsize)   do
	(
		local v = M3_Vertex()
		v.pos = ReadVec #v3d
		
		-- vertex bone weights
		for j = 1 to 4 do 
		(
			local w = ReadByte bstream #unsigned
			v.bw[j] = w / 255.0 
		) 
		
		-- vertex bone index
		for j = 1 to 4 do 
		(
			v.bi[j] = 1 + (ReadByte bstream #unsigned) -- 1 + as maxscript arrays are 1 based
		)

		-- First read in compressed normals
		for j = 1 to 4 do 
		(
			v.normal[j] = ReadByte bstream #unsigned
			v.normal[j] = (2 * v.normal[j] / 255.0) - 1
		)
		
		-- Convert to cartesian
		local vn = [0,0,0] -- need point3 when building mesh
		local w = v.normal[4]
		for j = 1 to 3 do
		(
			vn[j] = v.normal[j] / w
		)
		v.normal = vn
		
		-- Define UV conversion
		local uvm_sml 	= 2048.0
		for j=1 to 2 do 
		(
			uv = ReadShort bstream #signed
			uv = uv / uvm_sml
			--if uv > 1 then echo("Warning! Vert["+i as string+"].uv["+j as string+"]: "+uv as string+" is above 1!")
			if (j==2) and (flipuv_y) then (uv = 1 - uv) -- flip Y
			
			v.uv[j] = uv
		)
		
		SkipBytes bsize
		
		append vr v
	)
	
	echo ("nVerts: " + vr.count as string)
	
	return vr
)

fn M3_Read_DIV =
(
	step = "Read DIV"
	
	div = M3_DIV()
	div.faces = ReadRef flags:#ushort
	div.smeshes = ReadRef()
	div.bat = ReadRef()	
	div.msec = ReadRef()

	echo ("nFaces: " + div.faces.count as string)
	echo ("nSubmeshes: " + div.smeshes.count as string)
	
	return div
)

fn M3_Read_Submesh td =
(
	step = "Read Submeshes"
	
	smr = #()
	for i = 1 to td.nData do
	(
		sm = M3_Submesh()
		SkipBytes 4
		sm.indverts = ReadShort bstream #unsigned
		sm.nverts = ReadShort bstream #unsigned
		sm.indfaces = ReadLong bstream #unsigned
		sm.nfaces = ReadLong bstream #unsigned
		SkipBytes 12
			
		append smr sm
	)
	
	return smr
)

fn M3_Read_Sref td =
(
	step = "Read Submesh Material references"
	
	sr= #()
	for i = 1 to td.nData do
	(
		mat = M3_Sref()
		SkipBytes 4
		mat.subid = ReadShort bstream #unsigned + 1
		SkipBytes 4
		mat.matid = ReadShort bstream #unsigned + 1
		SkipBytes 2
		
		append sr mat
	)
	
	return sr
)

fn M3_Read_MATM th =
(
	step = "Read MATM"
	
	mtm = #()
	for i = 1 to th.nData do
	(
		matm = M3_MATM()
		matm.matind = ReadLong bstream #unsigned + 1
		matm.matref = ReadLong bstream #unsigned + 1
		
		append mtm matm
	)
	
	return mtm
)

fn M3_Read_LAYR = 
(
	l = M3_LAYR()
	
	SkipBytes 4
	ln = ReadRef() -- .dds file
	if (ln.count > 1) then l.name = M3_Name ln "/" else l.name = ln
	SkipBytes 340
	
	return l
)

fn M3_Read_Mat_Layrs =
(
	ml = M3_Mat_Layr()
	
	for j = 1 to 13 do
	(
		case (j) of
		(
			1: ml.diff = ReadRef()
			3: ml.spec = ReadRef()
			4: ml.emis = ReadRef()
			10: ml.norm = ReadRef()
			default: SkipBytes 8
		)
	)
	
	return ml
)

fn M3_Read_Mat td =
(
	step = "Read Materials"
	
	mr = #()
	for i = 1 to td.nData do
	(
		m = M3_Mat()
		m.name = ReadRef()
		--echo ("Mat_" + i as string + ": " + m.name)
		SkipBytes 40
		m.layrs = M3_Read_Mat_Layrs()
		SkipBytes 60
		
		append mr m
	)
	
	echo ("nMaterials: " + mr.count as string)	
	return mr
)

fn M3_Read_Data td flags = --Reading U32_, I32_, U8__, etc.
(
	local u = #()
	
	for i = 1 to td.nData do
	(
		local a
		case (flags) of
		(
			#animind: 
			(
				a 	= M3_Animoffs()
				a.ind		= ReadShort bstream #unsigned + 1
				a.flags 	= ReadShort bstream #unsigned
			)
			#ubyte: a = ReadByte bstream #unsigned
			#ushort: a = ReadShort bstream #unsigned
			#ulong: a = ReadLong bstream #unsigned 
		)
		
		append u a
	)
	
	return u
)

fn ReadTagData tagInd flags =
(
	local bm = ftell(bstream) -- bookmark first
	local d = #()
	th = tread[tagInd]

	if ((fseek bstream th.ofsData #seek_set) and (th.nData > 0)) then
	(
		case (th.dataID) of
        (
			"LDOM": d = M3_Read_MODL th
			"SQES": d = M3_Read_AnimData th
			"_CTS": d = M3_Read_SequenceData th
			"Q4DS": d = M3_Read_AnimBlock th
			"V3DS": d =M3_Read_AnimBlock th
			"3RDS": d = M3_Read_AnimBlock th
			"__8U" : d = M3_Read_Verts th flags
			"_VID": d = M3_Read_DIV()
			"_61U": d = M3_Read_Data th flags
			"_23U": d = M3_Read_Data th flags
			"_23I": d = M3_Read_Data th flags
			"3CEV": d = ReadVec #v3d array:th.nData
			"TAUQ": d = ReadVec #quat array:th.nData
			"NGER": d = M3_Read_Submesh th
			"_TAB": d = M3_Read_Sref th
			"MTAM": d = M3_Read_MATM th
			"_TAM": d = M3_Read_Mat th
			"RYAL": d = M3_Read_LAYR()
			"ENOB": d = M3_Read_Bones th
			"RAHC": d = ReadFixedString th.nData
			default: d = M3_Read_Data th #ubyte
		)
	)
	else
		"Read Tag failed!"
	
	fseek bstream bm #seek_set -- return to bookmark
	return d
)

-- ***************************
--  MAX SCENE FUNCTIONS
-- ***************************
fn M3_Bone_Depth b =
(
	-- For organising bones based on depth
	if b.parent == 0 then 0
	else return ( 1 + M3_Bone_Depth mread.bones[b.parent] )
)

fn M3_Create_Bones =
(
	---------------------- bones
	step = "Create Bones"
	echo "Creating bones..."
	cbones = #()
	
	mb = mread.bones
	for i = 1 to mb.count do
	(
		b = mb[i]
		--echo ("Creating bone_" + i as string + ": " + b.name)
		
		cb 				= BoneSys.createBone b.pos b.pos [0,0,0.1]
		cb.name 		= b.name
		cb.width 		= bonesize
		cb.height		= bonesize
		cb.showLinks	= true
		cb.boneScaleType = #none

		append cbones cb
	)
	max views redraw
	
	echo "Setting up bone hierarchy"
	for i=1 to mb.count do
	(
		b = mb[i]
		if b.parent!=0 then
		(
			-- echo ("Setting parent of " + i as string + " to " + (bones_read[i].par+1) as string)
			cbones[i].parent = cbones[b.parent]
		)
	)
	
	echo "Set up bone depth"
	---------------------- animation
	-- sort bones by depth
	local bd = #(); 
	for i=1 to cbones.count do
	(
		bonerec = [(M3_Bone_Depth mread.bones[i]), i]
		append bd bonerec
	)
	fn compfn a b = ( if a.x<b.x then return 1; else if a.x>b.x then return -1; else return 0; )
	qsort bd compfn
	
	echo "Set up bone transform"
	for i=1 to cbones.count do
	(
		local h = bd[i].y
		b = mread.bones[h]
		cb = cbones[h]
		
		in coordsys parent (cb.rotation = b.rot)
		in coordsys parent (cb.position = b.pos)
		in coordsys parent (cb.scale	= b.scale)
	)
	
	max views redraw
)

fn M3_Animate_Bone cb refid flags =
(
	-- 1. Find refid in animid list
	ar = aread[g_animid]
	bid = ar.animid
	local bfound = 0
	
	for i = 1 to bid.count do
	(
		if (bid[i] == refid) then
		(
			bfound = i
			-- more efficient for breaking for loop, 'break()' lags maxscript
			i = bid.count + 1
		)
	)
	
	-- 2. If refid found -> transform bone with corresponding animation data
	-- if not found -> bone refid references no animation data
	if (bfound != 0) then
	(
		-- get bone animation index from list
		bi = ar.animoffs[bfound].ind 
		--echo("cb: " + cb as string + " refid: " + refid as string)
		case (flags) of
		(
			#trans:
			(
				-- Translation
				bt = ar.trans[bi]

				for i = 1 to bt.frames.count do
				(
					t = M3_Convert_Time bt.frames[i]
					
					with animate on
					(			
						at time t 
						(
							in coordsys parent cb.pos = bt.keys[i] 
						) 
					)
				)
			)
			#rot:
			(
				-- Rotation
				br = ar.rot[bi]
				
				for i = 1 to br.frames.count do
				(
					t = M3_Convert_Time br.frames[i]
					
					with animate on
					(
						at time t 
						(
							in coordsys parent cb.rotation = br.keys[i] 
						) 
					)
				)
			)
		)
	)
)

fn M3_Animate_Bones =
(
	---------------------- animation
	-- sort bones by depth
	local bd = #(); 
	mb = mread.bones
	for i=1 to mb.count do
	(
		bonerec = [(M3_Bone_Depth mb[i]), i]
		append bd bonerec
	)
	fn compfn a b = ( if a.x<b.x then return 1; else if a.x>b.x then return -1; else return 0; )
	qsort bd compfn

	if (g_animid > mread.SEQS.count) then 
	(
		echo ("WARNING# AnimationID " + g_animid as string + " out of range! Set to final animation instead.")
		g_animid = mread.SEQS.count
	)
	adr = mread.SEQS[g_animid]
	
	-- Set max frames
	animationRange = interval 0 adr.maxframes
	
	echo ("Setting up animation " + adr.name + ", " + adr.maxframes as string + " frames...")
	echo "Transforming bones..."
	step = "Bone transforms"
	for k=1 to mb.count do
	(
		local i = bd[k].y
		--echo ("Doing bone " + i as string + " (depth: " + bd[k].x as string + ")" )

		--echo ("Transforming bone " + i as string)
		b = mread.bones[i]
		cb = cbones[i]
		-- translation
		M3_Animate_Bone cb b.transid #trans 
		-- rotation
		M3_Animate_Bone cb b.rotid #rot	
		
		-- cleanup
		gc()
	)
	echo "Bone animation done\n"
)

fn M3_Create_Mats =
(
	step = "Create Materials"
	
	echo "Creating Materials..."
	
	matlu = mread.DIV.bat
	cm = multimaterial numsubs:matlu.count
	for i = 1 to matlu.count do
	(
		-- find material referenced in lookup table
		mat_chk = matlu[i].matID
		mid = mread.matm[mat_chk].matref
		m = mread.mat[mid]
		
		local sm = standardMaterial name:(m.name)
		cm[i] = sm

		fn Assign_Bitmap texname =
		(
			bt = BitmapTexture()
			
			if (texname != 0) then 
			(
				-- Check max mapPaths for texture
				mcount = mapPaths.count()
				for i = 1 to mcount do
				(
					local tp = mapPaths.get i + "\\"
					
					tex = tp + texname
					if (doesFileExist(tex)) then 
					(
						bt.filename = tex
						i = mcount + 1
					)
					else if (i == mapPaths.count()) then
					(
						(
							echo ("WARNING# Texture "+ texname+" not found! Extract it manually from the MPQ to apply this texture to the model")
						)
					)
				)
			)
			
			return bt
		)
		
		sm.diffuseMap = Assign_Bitmap (m.layrs.diff.name)
		sm.specularMap = Assign_Bitmap (m.layrs.spec.name)
		sm.selfIllumMap = Assign_Bitmap (m.layrs.emis.name)
		if (sm.specularMap.filename != "") then sm.useSelfIllumColor = true
		sm.bumpMap = Assign_Bitmap (m.layrs.norm.name)
		
		showTextureMap cm[i] cm[i].diffuseMap on
	)
	
	return cm
)

fn M3_Create_Mesh =
(
	step = "Create Mesh"

	echo "Creating mesh..."

	v = #()
	f = #()
	t = #()
	mtl = #()

	vr = mread.verts 
	fr = mread.DIV.faces

	echo "Creating vertices..."

	-- build vertices and texcoords
	for i = 1 to vr.count do
	(
		append v vr[i].pos
		append t vr[i].uv
	)

	echo "Creating submeshes..."
	smr = mread.DIV.smeshes
	matlu = mread.DIV.bat
	for s = 1 to smr.count do
	(
		-- Building the Submeshes
		-- build faces by submesh
		-- (each submesh will be a material id)

		sm = smr[s]
		local up = sm.nfaces as integer
		local ind = sm.indfaces as integer
		--echo ("sm_"+s as string+".nfaces: "+up as string +" indfaces:" + sm.indfaces as string)

		if ((mod (up) 3) != 0.0 ) then echo "#ERROR sm.tris not a multiple of 3!"
		--else echo "#INFO sm.tris check passed!"
		
		--echo ("Creating Submesh_" + s as string)
		for i = 1 to (up) by 3 do
		(
			local a = fr[ind + i]  + 1
			local b = fr[ind + i+1]  + 1
			local c = fr[ind + i+2]  + 1
			
			local face = ( [a,b,c] as point3 )

			append f face
			append mtl matlu[s].subid
		)
	)

	echo "Creating mesh object"
	
	cmat = M3_Create_Mats()
	
	cmesh = mesh vertices:v faces:f materialIDs:mtl tverts:t name:(mread.name)
	cmesh.material = cmat
	cmesh.material.showInViewport = true
	setMeditMaterial 1 cmat
	
	update cmesh

	-- set normals
	for i = 1 to vr.count do
	(
		setNormal cmesh i vr[i].normal
	)
	
	-- tvert faces
	if vr.count != 0 do
	(
		step = "Build tv's"
		try
		(
			--Set texcoord faces 
			buildTVFaces cmesh false
			for i = 1 to f.count do
			(
				setTVFace cmesh i f[i]
			)
		)
		catch
		(
			echo (getCurrentException())
			throw ()
		)
	)
	update cmesh

	step = "Create Mesh Done"
)

fn M3_Apply_Skin =
(
	---------------------- skinning
	step = "Create Skin"
	echo "Applying skin to mesh..."

	m = cmesh
	select m

	max modify mode
	addModifier m (Skin name:"Skin")
	sk = m.modifiers[#Skin]
	
	modPanel.setCurrentObject sk

	-- 1. add all bones to the skin
	for j=1 to cbones.count do
	(
		skinOps.addBone sk cbones[j] -1
	)
	update m
	max views redraw

	-- Greatly speeds up vertex weight assignment processing
	disableSceneRedraw()
	
	-- 2. for each vertex, setup the bone weights
	for j=1 to mread.verts.count do
	(
		v = mread.verts[j]
		--echo (j as string + ": " + v.bi[1] as string + ", " + v.bi[2] as string + ", " + v.bi[3] as string + ", " + v.bi[4] as string \
		--	+ " --- (" + v.bw[1] as string + "," + v.bw[2] as string + "," + v.bw[3] as string + "," + v.bw[4] as string + ")")
		local lbi = #()
		local lbw = #()

		for h = 1 to 4 do
		(
			if v.bw[h]>0 then 
			( 
				k = v.bi[h]
				append lbi (mread.blist[k] + 1) 
				append lbw (v.bw[h])
			)
		)
		--echo ("j["+j as string+"].lbi: " + lbi as string + " lbw: " + lbw as string)

		skinOps.ReplaceVertexWeights sk j lbi lbw
	)
	enableSceneRedraw()
	
	update m
	redrawViews()
	step = "Skinning complete"
)

fn M3_Zoom_Model =
(
	step = "Zoom Viewports to Model"
	
	viewport.ZoomToBounds true cmesh.min cmesh.max
)
---
--- MAIN
-- Global UI Funcs
fn uiOpenFile ftypes &fname =
(
	local ret = getOpenFileName types:ftypes filename:fname
	if ret != undefined then fname = ret
)

-- Import
fn M3_Main file =
(	
	M3_Open(file)
	M3_Read_Header()
	M3_Read_Start()
	-- Mesh
	Try
	(
		if doCreateMesh then
		(
			M3_Create_Mesh()
			M3_Zoom_Model()
		)
	)
	Catch
	(
		echo "Mesh import failed!"
		echo ("****"+getCurrentException()+"****")
		doCreateMesh = false
		doCreateSkin = false
	)
	-- Bones
	Try 
	(
		if doCreateBones then M3_Create_Bones()
	)
	Catch
	(
		echo "Bone import failed!"
		echo ("****"+getCurrentException()+"****")
		doCreateBones = false
		doCreateSkin = false
		doTransformBones = false
	)
	-- Skin
	Try 
	(
		if doCreateBones and doCreateSkin and doCreateMesh then M3_Apply_Skin()
	)
	Catch
	(
		echo "Skin creation failed!"
		echo ("****"+getCurrentException()+"****")
		doCreateBones = false
		doCreateSkin = false
		doTransformBones = false
	)
	-- Bone Animation
	Try
	(
		if doCreateBones and doTransformBones then M3_Animate_Bones()
	)
	Catch
	(
		echo "Bone animation failed!"
		echo ("****"+getCurrentException()+"****")
		doTransformBones = false
	)
	M3_Close()
	echo "======== Done ========\n"

	max views redraw
)

utility m3imp "SC2 M3 Import"
(
	group "Model Filename"
	(
		button bOpenFile "Open..."
		edittext tFileName
	)
	
	checkBox chkImportBones "Import Bones" check:(doCreateBones) tooltip:"Imports Bones from Model (buggy)"
	checkBox chkTransformBones "Animate Bones" check:(doTransformBones) tooltip:"Animates model bones"
	spinner spnAnimID "Animation ID:" range:[1,220,1] type:#integer
	spinner spnFPS "FPS:" range:[1,60,30] type:#integer
	
	button bImport "Import" height:35 width:100
	
	on m3imp open do
	(
		if (chkImportBones.checked == false) then
		(
			chkTransformBones.checked = false 	
			chkTransformBones.enabled	= false
			spnAnimID.enabled = false
			spnFPS.enabled = false
		)
	)
	on chkImportBones changed false do
	(
		chkTransformBones.checked = false 	
		chkTransformBones.enabled	= false
		spnAnimID.enabled = false
		spnFPS.enabled = false
	)
	on chkImportBones changed true do
	(
		chkTransformBones.enabled	= true
		spnAnimID.enabled = true
		spnFPS.enabled = true
	)
	on chkTransformBones changed true do
	(
		spnAnimID.enabled = true
		spnFPS.enabled = true
	)
	on chkTransformBones changed false do
	(
		spnAnimID.enabled = false
		spnFPS.enabled = false
	)
	on bOpenFile pressed do
	(
		uiOpenFile "M3 model (*.m3)|*.m3|All Files|*.*|" &tFileName.text
	)
	on bImport pressed do
	(
		doCreateBones = chkImportBones.checked
		doTransformBones = chkTransformBones.checked
		g_animid = spnAnimID.value
		useFPS = spnFPS.value
		if doesFileExist(tFilename.text) then M3_Main(tFilename.text)
	)
)
