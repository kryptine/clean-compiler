
#include <AppleEvents.h>
#include <AERegistry.h>

static char *result_string;
static int n_free_result_string_characters;

static pascal OSErr DoAEOpenApplication (AppleEvent *theAppleEvent,AppleEvent *replyAppleEvent,long refCon)
{
	return noErr;
}

static int has_required_parameters (AppleEvent *theAppleEvent)
{
	Size actual_size;
	DescType returned_type;
	OSErr r;
	
	r=AEGetAttributePtr (theAppleEvent,keyMissedKeywordAttr,typeWildCard,&returned_type,NULL,0,&actual_size);
	if (r==errAEDescNotFound)
		return noErr;
	if (r==noErr)
		r=errAEEventNotHandled;
	return r;
}

static pascal OSErr DoAEOpenDocuments (AppleEvent *theAppleEvent,AppleEvent *replyAppleEvent, long refCon)
{
	OSErr r;
	AEDescList document_list;

	if (n_free_result_string_characters<4){
		n_free_result_string_characters=0;
		result_string=NULL;
		return 0;
	}

	result_string[0]='O';
	result_string[1]='P';
	result_string[2]='E';
	result_string[3]='N';		
	result_string+=4;
	n_free_result_string_characters-=4;
	
	r=AEGetParamDesc (theAppleEvent,keyDirectObject,typeAEList,&document_list);
	
	if (r==noErr){
		r=has_required_parameters (theAppleEvent);

		if (r==noErr){
			long n_items;
		
			r=AECountItems (&document_list,&n_items);
						
			if (r==noErr){
				long i;
				
				for (i=1; i<=n_items; ++i){
					AEKeyword keyword;
					DescType returned_type;
					FSSpec fss;
					Size actual_size;
					int n;

					r=AEGetNthPtr (&document_list,i,typeFSS,&keyword,&returned_type,&fss,sizeof (FSSpec),&actual_size);
					
					if (r!=noErr)
						break;
					
					if (n_free_result_string_characters<sizeof (FSSpec)){
						AEDisposeDesc (&document_list);
						n_free_result_string_characters=0;
						result_string=NULL;
						return 0;
					}
					
					*(FSSpec*)result_string=fss;
					result_string+=sizeof (FSSpec);
					n_free_result_string_characters-=sizeof (FSSpec);
				}
			}
		}
	}

	AEDisposeDesc (&document_list);

	if (r!=noErr){
		result_string=NULL;
		n_free_result_string_characters=0;
	}
	
	return r;
}
 
static pascal OSErr DoAEPrintDocuments (AppleEvent *theAppleEvent,AppleEvent *replyAppleEvent,long refCon)
{
	return errAEEventNotHandled;
}
 
static pascal OSErr DoAEQuitApplication (AppleEvent *theAppleEvent,AppleEvent *replyAppleEvent,long refCon)
{
	if (n_free_result_string_characters>=4){
		result_string[0]='Q';
		result_string[1]='U';
		result_string[2]='I';
		result_string[3]='T';		
		result_string+=4;
		n_free_result_string_characters-=4;
	}
	return noErr;
}

extern pascal OSErr do_script_apple_event (AppleEvent *apple_event,AppleEvent *replyAppleEvent,long refCon);

extern int clean2_compile (int);

static pascal OSErr DoAEScript (AppleEvent *apple_event,AppleEvent *replyAppleEvent,long refCon)
{
	DescType returned_type;
	long actual_size;
	int error;
	char *result_string_begin;

	result_string_begin=result_string;
	
	if (n_free_result_string_characters>=6){
		result_string[0]='S';
		result_string[1]='C';
		result_string[2]='R';
		result_string[3]='I';
		result_string[4]='P';
		result_string[5]='T';
		result_string+=6;
		n_free_result_string_characters-=6;
	}

	error=AEGetParamPtr (apple_event,keyDirectObject,'TEXT',&returned_type,result_string,n_free_result_string_characters,&actual_size);

	if (error!=noErr || actual_size > n_free_result_string_characters){
		result_string=NULL;
		n_free_result_string_characters=0;
	} else

	/* RWS ... : ugly, special case for Clean IDE / cg combo */
	if (strncmp (result_string, "cg ", 3) == 0)
	{
		return do_script_apple_event (apple_event, replyAppleEvent, refCon);
	}
	/* ... RWS */
	else if (strncmp (result_string,"cocl ",5)==0){
		int string_length;
		
		result_string += actual_size;
		string_length=result_string-result_string_begin;

		result_string=NULL;

		return clean2_compile (string_length);
	}

	result_string	+= actual_size;

	return 1;
}

int install_apple_event_handlers (void)
{
	OSErr r;

	r=AEInstallEventHandler (kCoreEventClass,kAEOpenApplication,NewAEEventHandlerProc (DoAEOpenApplication),0,false);

	if (r==noErr)
		r=AEInstallEventHandler (kCoreEventClass,kAEOpenDocuments,NewAEEventHandlerProc (DoAEOpenDocuments),0,false);

	if (r==noErr)
		r=AEInstallEventHandler (kCoreEventClass,kAEPrintDocuments,NewAEEventHandlerProc (DoAEPrintDocuments),0,false);

	if (r==noErr)
		r=AEInstallEventHandler (kCoreEventClass,kAEQuitApplication,NewAEEventHandlerProc (DoAEQuitApplication),0,false);

	if (r==noErr)
		r=AEInstallEventHandler (kAEMiscStandards,kAEDoScript,NewAEEventHandlerProc (DoAEScript),0,false);
	
	return r;
}

int handle_apple_event (EventRecord *event_p,long *clean_string)
{	
	char *string;
	int string_length;
	
	string_length=clean_string[1];
	string=(char*)&clean_string[2];

	result_string=string;
	n_free_result_string_characters=string_length;

	AEProcessAppleEvent (event_p);

	if (result_string!=NULL)
		string_length=result_string-string;
	else
		string_length=0;
	
	result_string=NULL;
	n_free_result_string_characters=0;

	return string_length;
}

static char apple_event_string[2052];

int handle_apple_event2 (int what,int message,int when,int p1,int p2,int modifiers)
{
	EventRecord event;
	char *string;
	int string_length;

	event.what=what;
	event.message=message;
	event.when=when;
	event.where.h=p1;
	event.where.v=p2;
	event.modifiers=modifiers;
	
	string_length=2048;
	string=apple_event_string;

	result_string=string;
	n_free_result_string_characters=string_length;

	AEProcessAppleEvent (&event);

	if (result_string!=NULL)
		string_length=result_string-string;
	else
		string_length=0;
	
	result_string=NULL;
	n_free_result_string_characters=0;

	return string_length;
}

int get_apple_event_string (int length,long *clean_string)
{
	char *string;
	int string_length;
	
	string_length=clean_string[0];
	string=(char*)&clean_string[1];

	if (length==string_length){
		int i;
		
		for (i=0; i<string_length; ++i)
			string[i]=apple_event_string[i];
	} else
		string_length=0;

	return string_length;
}
