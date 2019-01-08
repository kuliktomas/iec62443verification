------------------------------ MODULE vehiclecloud ------------------------------

EXTENDS Naturals, TLC, Sequences, FiniteSets

CONSTANTS

(* All user IDs *)
ALL_USER_IDS

(* Used to indicate the absence of a user *)
NO_USER == 0

ASSUME
(* User IDs that are different from NO_USER must exist *)
Cardinality(ALL_USER_IDS) > 0 /\ \A id \in ALL_USER_IDS: id /= NO_USER

(* --algorithm VehicleCloud

variables

    \* Set by the cloud in order to decide whether a client request is allowed
    clientAuthorised = FALSE;
  
    \* Determines whether the client is in the process of fetching data from the operations terminal (via the cloud)
    clientViewingData = FALSE;
    
    \* The ID of the user currently accessing the system via the client
    clientCurrentUserId = NO_USER;
    
    \* Determines whether the cloud have checked (or validated) the client id for some request (synchronisation variable)
    \* Related to this, the variable 'clientAuthorised' indicates whether the client request is allowed.
    interactiveCloudCheckedId = FALSE;
    
    \* Determines whether the cloud has delived the firmware to the operations terminal
    interactiveCloudDeliveredFirmware = FALSE;
    
    \* Determines whether the cloud has sent a firmware acknowledgement to the client (synchronisation variable)
    interactiveCloudFirmwareAckSent = FALSE;
    
    \* True if location A (the only location that we model) is suspended, false otherwise
    interactiveCloudLocationSuspended \in {TRUE, FALSE};
    
    \* True if the ID of the client is trusted, false otherwise.
    clientIdTrusted \in {TRUE, FALSE};
    
    \* True when the service cloud has received new data from the operations terminal (synchronisation variable)  
    serviceCloudDataReceived = FALSE;
    
    \* The most recent data that the service cloud has received from the operations terminal
    serviceCloudDataSnapshot = FALSE;
    
    \* Determines whether the gateway allows inwards communication
    gatewayInwardsOpen = FALSE;
    
    \* Determines whether the gateway has sent a firmware acknowledgement (synchronisation variable)
    gatewayFirmwareAckSent = FALSE;
    
    \* Determines whether the gateway has delivered the firmware to the operations terminal
    gatewayDeliveredFirmware = FALSE;
    
    \* True if the ID of the gateway is trusted, false otherwise.
    gatewayIdTrusted \in {TRUE, FALSE};
  
    \* Determines whether the operations terminal has sent a firmware acknowledgement to the cloud (synchronisation variable)
    otFirmwareAckSent = FALSE;
    
    \* The most recent data sent by the operations terminal.
    \* The operations terminal simply toggles this variable every time data is sent.
    \* This allows us to confirm that the service cloud receives different data 
    otLatestData = FALSE;
    
    \* True if the operations terminal has sent new data to the service cloud (synchronisation variable)
    otDataSentToServiceCloud = FALSE;
    
    \* Determines whether the latest data has been signed by the operations terminal
    otDataSigned = FALSE;
    
    \* Used for storing (valid) firmware received from the client
    otStorage = NO_FIRMWARE;
        
    otDataRedirected = FALSE;
    
    otDataTransmissionBlocked = FALSE;

    \* A copy of the firmware used by the control network
    otInstalledFirmware =   LET timeStamp == 1
                            IN
                                <<timeStamp, ValidFirmware>>;
    
    \* True if someone inserted a USB device and failed to provide the authorisation password within a safety time limit. False otherwise
    otUsbUnauthorisedAccess = FALSE;
    
    \* Determines whether the cloud has sent data to the client (synchronisation variable)
    cloudDataSent = FALSE;
    
    \* Firmware that the client will upload to the operations terminal
    clientFirmware = NO_FIRMWARE;
    
    controlNetworkDataSendToOT = FALSE;
    
    controlNetworkLatestData = FALSE;
    
    controlNetworkDataEncrypted = FALSE;

define

    \* Processes
    GATEWAY == 1
    OT == 2
    INTERACTIVE_CLOUD == 4
    CLIENT == 5
    SERVICE_CLOUD == 6
    CONTROL_NETWORK == 7
    
    \* Used to indicate the absence of client firmware
    NO_FIRMWARE == <<>>
    
    \* Set of all firmwares
    AllFirmware == [ signatureValid : BOOLEAN, genuine : BOOLEAN, size : BOOLEAN ]
    
    \* True if the client is sending firmware, false otherwise
    ClientSendingFirmware == clientFirmware /= NO_FIRMWARE
    
    \* Has any client request been sent?    
    ClientRequestSent == ClientSendingFirmware \/ clientViewingData
    
    \* The firmware timestamp index
    FirmwareTimestampIndex == 1
    
    \* The firmware value index   
    FirmwareValueIndex == 2
    
    \* For a piece of firmware to be considered valid it must have a valid signature, be genuine and fit the operations terminal storage
    ValidFirmware == [signatureValid |-> TRUE, genuine |-> TRUE, size |-> TRUE]
    
    \* Check that 'firmware' is valid
    FirmwareValid(firmware) ==  firmware /= NO_FIRMWARE /\
                                firmware[FirmwareValueIndex].signatureValid /\
                                firmware[FirmwareValueIndex].genuine /\
                                firmware[FirmwareValueIndex].size

    \* Check that firmware signature is valid
    FirmwareHasValidSignature(firmware) == firmware[FirmwareValueIndex].signatureValid
    
    \* Check that firmware is genuine
    FirmwareIsGenuine(firmware) == firmware[FirmwareValueIndex].genuine
    
    \* Check that the firmware fits the operations terminal storage
    FirmwareFitsStorage(firmware) == firmware[FirmwareValueIndex].size

    \* Compute next firmware timestamp
    NextFirmwareTimestamp ==    LET currentTimeStamp == otInstalledFirmware[FirmwareTimestampIndex]
                                IN
                                    IF currentTimeStamp = 1 THEN 2 ELSE 3
    
    \* Determines whether the service cloud has waited too long for the operations terminal to deliver the data.
    \* Since we don't model time explicitly, we simply say that the time limit has passed once the
    \* data has been redirected to some sink
    DataDeliveryTimeElapsed == otDataRedirected

end define

fair process client = CLIENT

variable
    \* Used to store data fetched from the service cloud
    clientData = FALSE
begin
ClientBegin:

    with id \in ALL_USER_IDS do
        clientCurrentUserId := id;
    end with;
    
    either ClientSendFirmwareUpdate:
        \* Get firmware to send
        with clientFirmwareToSend \in AllFirmware do
            clientFirmware := <<NextFirmwareTimestamp, clientFirmwareToSend>>;
        end with;
    or ClientViewData:
        \* Fetch newest data
        clientViewingData := TRUE;
    end either;
    
    \* Wait for cloud to check id
    ClientAwaitingIdCheck:
        await interactiveCloudCheckedId;
        
    if clientAuthorised then
        \* Wait for firmware acknowledgement
        if ClientSendingFirmware then
            ClientAwaitingFirmwareAck:
                await interactiveCloudFirmwareAckSent;
                clientFirmware := NO_FIRMWARE;        
        elsif clientViewingData then
            ClientUpdateData:
                await cloudDataSent;
                clientData := serviceCloudDataSnapshot;
                cloudDataSent := FALSE;
        end if;
                
    end if;
end process

fair process serviceCloud = SERVICE_CLOUD
begin
ServiceCloudBegin:
    await otDataSentToServiceCloud \/ DataDeliveryTimeElapsed;
    
    if DataDeliveryTimeElapsed then
        \* Security measure: prevent operations terminal from sending data
        otDataTransmissionBlocked := TRUE;
        goto ServiceCloudDone;
    else
        ServiceCloudReceiveData:
            with oldData = serviceCloudDataSnapshot do
                \* The data must be new
                if otDataSigned /\ gatewayIdTrusted then
                    serviceCloudDataSnapshot := otLatestData;
                end if;
                \* If the data is not signed by the operations terminal the data snapshot will not be updated
                assert (~otDataSigned) => (serviceCloudDataSnapshot = oldData);
            serviceCloudDataReceived := TRUE;
            otDataSentToServiceCloud := FALSE;
            end with;
    end if;
    ServiceCloudEndCycle:
        \* Repeat
        goto ServiceCloudBegin;
    ServiceCloudDone:
        skip;
        
end process;

fair process interactiveCloud = INTERACTIVE_CLOUD
begin
InteractiveCloudBegin:
    await ClientRequestSent;
    
    if interactiveCloudLocationSuspended then
        \* Location A is already suspended
        clientAuthorised := FALSE;
        interactiveCloudCheckedId := TRUE;
    else
        \* Location A is not suspended
        if clientIdTrusted then
        
            clientAuthorised := TRUE;
            interactiveCloudCheckedId := TRUE;
                
            if ClientSendingFirmware then
                    
                InteractiveCloudAttemptSendingFirmware:
                    \* Send firmware
                    interactiveCloudDeliveredFirmware := TRUE;
                    \* ACKFWUpdate
                    CloudAwaitingFirmwareAck:
                        await gatewayFirmwareAckSent;
        
                        InteractiveCloudRelayFirmwareAck: 
                            interactiveCloudFirmwareAckSent := TRUE;
            else
                InteractiveCloudDeliverData:
                    assert clientViewingData;
                    cloudDataSent := TRUE;
                    \* The service cloud is responsible for fetching the most recent data from the operations terminal
            end if
    
        else
            assert ~interactiveCloudLocationSuspended;
            \* Location A is now suspended
            interactiveCloudLocationSuspended := TRUE;
            clientAuthorised := FALSE;
            interactiveCloudCheckedId := TRUE;
        end if;
    end if;
end process;

fair process gateway = GATEWAY
begin
    GatewayAwaitingFirmware:
        \* Proceed once the firmware has been received, or when the client cloud has terminated.
        \* If we proceed due to client cloud termination it simply means that the client was viewing data,
        \* hence no client-to-vehicle communication is needed. In that case, the gateway can terminate.
        await interactiveCloudDeliveredFirmware \/ pc[INTERACTIVE_CLOUD] = "Done";
    
    if interactiveCloudDeliveredFirmware then
        
        with b \in {TRUE, FALSE} do
            gatewayInwardsOpen := b;
        end with;
        
        if gatewayInwardsOpen then
            assert clientAuthorised;
            gatewayDeliveredFirmware := TRUE;
        
            GatewayAwaitingFirmwareAck:
                await otFirmwareAckSent;
        end if;
            
        GatewayAwaitingOT:
            gatewayFirmwareAckSent := TRUE;
    end if;
     
end process;

fair process ot = OT
begin
OTBegin:
    skip;
    OTReceiveData:
        await controlNetworkDataSendToOT;
        \* The data has changed
        assert otLatestData /= controlNetworkLatestData;
        \* The raw data is received
        assert ~controlNetworkDataEncrypted;
        otLatestData := controlNetworkLatestData;
        \* Encrypt the data received from the control network
        controlNetworkDataEncrypted := TRUE;
        controlNetworkDataSendToOT := FALSE;
    OTSendData:
        if ~otDataTransmissionBlocked then
            \* Send data
            with b \in {TRUE, FALSE} do
                otDataSigned := b;
            end with;
            serviceCloudDataReceived := FALSE;
            either OTSendToServiceCloud:
                otDataSentToServiceCloud := TRUE;
                assert ~otDataRedirected;
                OTAwaitingServiceCloud:
                    await serviceCloudDataReceived;
            or OTRedirectData:
                otDataRedirected := TRUE;
                assert ~otDataSentToServiceCloud;
            end either;
            OTFinishSendingData:
                otDataRedirected := FALSE;
        else
            OTLogDataBlock:
                skip;
        end if;
    OTReadUSB:
        \* USB connected
        \* Security log: USB connected
        either OTUSBConnected:
            either OTPasswordOK:
                either OTUSBHasFirmware:
                    with usbFirmware \in AllFirmware do
                        with usbFirmwareTimestamped = <<NextFirmwareTimestamp, usbFirmware>> do
                            if FirmwareValid(usbFirmwareTimestamped) then
                                otStorage := usbFirmwareTimestamped;
                            end if; 
                        end with;
                    end with;
                or OTUSBHasNoFirmware:
                    \* Nothing to do
                    skip;
                end either;
            or OTPasswordNotOk:
                otUsbUnauthorisedAccess := TRUE;
                OTUsbSecurityEventReset:
                    otUsbUnauthorisedAccess := FALSE;
            end either;
        or OTUSBNotConnected:
            skip;
        end either;
    OTReceiveFirmware:
        if gatewayDeliveredFirmware then
            if FirmwareValid(clientFirmware) then
                                otStorage := clientFirmware;
            end if; 
            OTSendAck:
                otFirmwareAckSent := TRUE;
                \* Expect new firmware
                interactiveCloudDeliveredFirmware := FALSE;
                gatewayDeliveredFirmware := FALSE;
        end if;
    OTHandlePendingRequests:
            goto OTBegin;
    
end process;

fair process controlNetwork = CONTROL_NETWORK
begin
ControlNetworkBegin:
    skip;
    ControlNetworkSendData:
        \* At this point the control network data is not encrypted
        controlNetworkDataEncrypted := FALSE;
        controlNetworkLatestData := ~controlNetworkLatestData;
        controlNetworkDataSendToOT := TRUE;
        ControlNetworkAwaitingOT:
            await ~controlNetworkDataSendToOT;
        skip;
    ControlNetworkHandlePendingRequests:
        goto ControlNetworkBegin;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES clientAuthorised, clientViewingData, clientCurrentUserId, 
          interactiveCloudCheckedId, interactiveCloudDeliveredFirmware, 
          interactiveCloudFirmwareAckSent, interactiveCloudLocationSuspended, 
          clientIdTrusted, serviceCloudDataReceived, serviceCloudDataSnapshot, 
          gatewayInwardsOpen, gatewayFirmwareAckSent, 
          gatewayDeliveredFirmware, gatewayIdTrusted, otFirmwareAckSent, 
          otLatestData, otDataSentToServiceCloud, otDataSigned, otStorage, 
          otDataRedirected, otDataTransmissionBlocked, otInstalledFirmware, 
          otUsbUnauthorisedAccess, cloudDataSent, clientFirmware, 
          controlNetworkDataSendToOT, controlNetworkLatestData, 
          controlNetworkDataEncrypted, pc

(* define statement *)
GATEWAY == 1
OT == 2
INTERACTIVE_CLOUD == 4
CLIENT == 5
SERVICE_CLOUD == 6
CONTROL_NETWORK == 7


NO_FIRMWARE == <<>>


AllFirmware == [ signatureValid : BOOLEAN, genuine : BOOLEAN, size : BOOLEAN ]


ClientSendingFirmware == clientFirmware /= NO_FIRMWARE


ClientRequestSent == ClientSendingFirmware \/ clientViewingData


FirmwareTimestampIndex == 1


FirmwareValueIndex == 2


ValidFirmware == [signatureValid |-> TRUE, genuine |-> TRUE, size |-> TRUE]


FirmwareValid(firmware) ==  firmware /= NO_FIRMWARE /\
                            firmware[FirmwareValueIndex].signatureValid /\
                            firmware[FirmwareValueIndex].genuine /\
                            firmware[FirmwareValueIndex].size


FirmwareHasValidSignature(firmware) == firmware[FirmwareValueIndex].signatureValid


FirmwareIsGenuine(firmware) == firmware[FirmwareValueIndex].genuine


FirmwareFitsStorage(firmware) == firmware[FirmwareValueIndex].size


NextFirmwareTimestamp ==    LET currentTimeStamp == otInstalledFirmware[FirmwareTimestampIndex]
                            IN
                                IF currentTimeStamp = 1 THEN 2 ELSE 3




DataDeliveryTimeElapsed == otDataRedirected

VARIABLE clientData

vars == << clientAuthorised, clientViewingData, clientCurrentUserId, 
           interactiveCloudCheckedId, interactiveCloudDeliveredFirmware, 
           interactiveCloudFirmwareAckSent, interactiveCloudLocationSuspended, 
           clientIdTrusted, serviceCloudDataReceived, 
           serviceCloudDataSnapshot, gatewayInwardsOpen, 
           gatewayFirmwareAckSent, gatewayDeliveredFirmware, gatewayIdTrusted, 
           otFirmwareAckSent, otLatestData, otDataSentToServiceCloud, 
           otDataSigned, otStorage, otDataRedirected, 
           otDataTransmissionBlocked, otInstalledFirmware, 
           otUsbUnauthorisedAccess, cloudDataSent, clientFirmware, 
           controlNetworkDataSendToOT, controlNetworkLatestData, 
           controlNetworkDataEncrypted, pc, clientData >>

ProcSet == {CLIENT} \cup {SERVICE_CLOUD} \cup {INTERACTIVE_CLOUD} \cup {GATEWAY} \cup {OT} \cup {CONTROL_NETWORK}

Init == (* Global variables *)
        /\ clientAuthorised = FALSE
        /\ clientViewingData = FALSE
        /\ clientCurrentUserId = NO_USER
        /\ interactiveCloudCheckedId = FALSE
        /\ interactiveCloudDeliveredFirmware = FALSE
        /\ interactiveCloudFirmwareAckSent = FALSE
        /\ interactiveCloudLocationSuspended \in {TRUE, FALSE}
        /\ clientIdTrusted \in {TRUE, FALSE}
        /\ serviceCloudDataReceived = FALSE
        /\ serviceCloudDataSnapshot = FALSE
        /\ gatewayInwardsOpen = FALSE
        /\ gatewayFirmwareAckSent = FALSE
        /\ gatewayDeliveredFirmware = FALSE
        /\ gatewayIdTrusted \in {TRUE, FALSE}
        /\ otFirmwareAckSent = FALSE
        /\ otLatestData = FALSE
        /\ otDataSentToServiceCloud = FALSE
        /\ otDataSigned = FALSE
        /\ otStorage = NO_FIRMWARE
        /\ otDataRedirected = FALSE
        /\ otDataTransmissionBlocked = FALSE
        /\ otInstalledFirmware = (LET timeStamp == 1
                                  IN
                                      <<timeStamp, ValidFirmware>>)
        /\ otUsbUnauthorisedAccess = FALSE
        /\ cloudDataSent = FALSE
        /\ clientFirmware = NO_FIRMWARE
        /\ controlNetworkDataSendToOT = FALSE
        /\ controlNetworkLatestData = FALSE
        /\ controlNetworkDataEncrypted = FALSE
        (* Process client *)
        /\ clientData = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = CLIENT -> "ClientBegin"
                                        [] self = SERVICE_CLOUD -> "ServiceCloudBegin"
                                        [] self = INTERACTIVE_CLOUD -> "InteractiveCloudBegin"
                                        [] self = GATEWAY -> "GatewayAwaitingFirmware"
                                        [] self = OT -> "OTBegin"
                                        [] self = CONTROL_NETWORK -> "ControlNetworkBegin"]

ClientBegin == /\ pc[CLIENT] = "ClientBegin"
               /\ \E id \in ALL_USER_IDS:
                    clientCurrentUserId' = id
               /\ \/ /\ pc' = [pc EXCEPT ![CLIENT] = "ClientSendFirmwareUpdate"]
                  \/ /\ pc' = [pc EXCEPT ![CLIENT] = "ClientViewData"]
               /\ UNCHANGED << clientAuthorised, clientViewingData, 
                               interactiveCloudCheckedId, 
                               interactiveCloudDeliveredFirmware, 
                               interactiveCloudFirmwareAckSent, 
                               interactiveCloudLocationSuspended, 
                               clientIdTrusted, serviceCloudDataReceived, 
                               serviceCloudDataSnapshot, gatewayInwardsOpen, 
                               gatewayFirmwareAckSent, 
                               gatewayDeliveredFirmware, gatewayIdTrusted, 
                               otFirmwareAckSent, otLatestData, 
                               otDataSentToServiceCloud, otDataSigned, 
                               otStorage, otDataRedirected, 
                               otDataTransmissionBlocked, otInstalledFirmware, 
                               otUsbUnauthorisedAccess, cloudDataSent, 
                               clientFirmware, controlNetworkDataSendToOT, 
                               controlNetworkLatestData, 
                               controlNetworkDataEncrypted, clientData >>

ClientSendFirmwareUpdate == /\ pc[CLIENT] = "ClientSendFirmwareUpdate"
                            /\ \E clientFirmwareToSend \in AllFirmware:
                                 clientFirmware' = <<NextFirmwareTimestamp, clientFirmwareToSend>>
                            /\ pc' = [pc EXCEPT ![CLIENT] = "ClientAwaitingIdCheck"]
                            /\ UNCHANGED << clientAuthorised, 
                                            clientViewingData, 
                                            clientCurrentUserId, 
                                            interactiveCloudCheckedId, 
                                            interactiveCloudDeliveredFirmware, 
                                            interactiveCloudFirmwareAckSent, 
                                            interactiveCloudLocationSuspended, 
                                            clientIdTrusted, 
                                            serviceCloudDataReceived, 
                                            serviceCloudDataSnapshot, 
                                            gatewayInwardsOpen, 
                                            gatewayFirmwareAckSent, 
                                            gatewayDeliveredFirmware, 
                                            gatewayIdTrusted, 
                                            otFirmwareAckSent, otLatestData, 
                                            otDataSentToServiceCloud, 
                                            otDataSigned, otStorage, 
                                            otDataRedirected, 
                                            otDataTransmissionBlocked, 
                                            otInstalledFirmware, 
                                            otUsbUnauthorisedAccess, 
                                            cloudDataSent, 
                                            controlNetworkDataSendToOT, 
                                            controlNetworkLatestData, 
                                            controlNetworkDataEncrypted, 
                                            clientData >>

ClientViewData == /\ pc[CLIENT] = "ClientViewData"
                  /\ clientViewingData' = TRUE
                  /\ pc' = [pc EXCEPT ![CLIENT] = "ClientAwaitingIdCheck"]
                  /\ UNCHANGED << clientAuthorised, clientCurrentUserId, 
                                  interactiveCloudCheckedId, 
                                  interactiveCloudDeliveredFirmware, 
                                  interactiveCloudFirmwareAckSent, 
                                  interactiveCloudLocationSuspended, 
                                  clientIdTrusted, serviceCloudDataReceived, 
                                  serviceCloudDataSnapshot, gatewayInwardsOpen, 
                                  gatewayFirmwareAckSent, 
                                  gatewayDeliveredFirmware, gatewayIdTrusted, 
                                  otFirmwareAckSent, otLatestData, 
                                  otDataSentToServiceCloud, otDataSigned, 
                                  otStorage, otDataRedirected, 
                                  otDataTransmissionBlocked, 
                                  otInstalledFirmware, otUsbUnauthorisedAccess, 
                                  cloudDataSent, clientFirmware, 
                                  controlNetworkDataSendToOT, 
                                  controlNetworkLatestData, 
                                  controlNetworkDataEncrypted, clientData >>

ClientAwaitingIdCheck == /\ pc[CLIENT] = "ClientAwaitingIdCheck"
                         /\ interactiveCloudCheckedId
                         /\ IF clientAuthorised
                               THEN /\ IF ClientSendingFirmware
                                          THEN /\ pc' = [pc EXCEPT ![CLIENT] = "ClientAwaitingFirmwareAck"]
                                          ELSE /\ IF clientViewingData
                                                     THEN /\ pc' = [pc EXCEPT ![CLIENT] = "ClientUpdateData"]
                                                     ELSE /\ pc' = [pc EXCEPT ![CLIENT] = "Done"]
                               ELSE /\ pc' = [pc EXCEPT ![CLIENT] = "Done"]
                         /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                         clientCurrentUserId, 
                                         interactiveCloudCheckedId, 
                                         interactiveCloudDeliveredFirmware, 
                                         interactiveCloudFirmwareAckSent, 
                                         interactiveCloudLocationSuspended, 
                                         clientIdTrusted, 
                                         serviceCloudDataReceived, 
                                         serviceCloudDataSnapshot, 
                                         gatewayInwardsOpen, 
                                         gatewayFirmwareAckSent, 
                                         gatewayDeliveredFirmware, 
                                         gatewayIdTrusted, otFirmwareAckSent, 
                                         otLatestData, 
                                         otDataSentToServiceCloud, 
                                         otDataSigned, otStorage, 
                                         otDataRedirected, 
                                         otDataTransmissionBlocked, 
                                         otInstalledFirmware, 
                                         otUsbUnauthorisedAccess, 
                                         cloudDataSent, clientFirmware, 
                                         controlNetworkDataSendToOT, 
                                         controlNetworkLatestData, 
                                         controlNetworkDataEncrypted, 
                                         clientData >>

ClientAwaitingFirmwareAck == /\ pc[CLIENT] = "ClientAwaitingFirmwareAck"
                             /\ interactiveCloudFirmwareAckSent
                             /\ clientFirmware' = NO_FIRMWARE
                             /\ pc' = [pc EXCEPT ![CLIENT] = "Done"]
                             /\ UNCHANGED << clientAuthorised, 
                                             clientViewingData, 
                                             clientCurrentUserId, 
                                             interactiveCloudCheckedId, 
                                             interactiveCloudDeliveredFirmware, 
                                             interactiveCloudFirmwareAckSent, 
                                             interactiveCloudLocationSuspended, 
                                             clientIdTrusted, 
                                             serviceCloudDataReceived, 
                                             serviceCloudDataSnapshot, 
                                             gatewayInwardsOpen, 
                                             gatewayFirmwareAckSent, 
                                             gatewayDeliveredFirmware, 
                                             gatewayIdTrusted, 
                                             otFirmwareAckSent, otLatestData, 
                                             otDataSentToServiceCloud, 
                                             otDataSigned, otStorage, 
                                             otDataRedirected, 
                                             otDataTransmissionBlocked, 
                                             otInstalledFirmware, 
                                             otUsbUnauthorisedAccess, 
                                             cloudDataSent, 
                                             controlNetworkDataSendToOT, 
                                             controlNetworkLatestData, 
                                             controlNetworkDataEncrypted, 
                                             clientData >>

ClientUpdateData == /\ pc[CLIENT] = "ClientUpdateData"
                    /\ cloudDataSent
                    /\ clientData' = serviceCloudDataSnapshot
                    /\ cloudDataSent' = FALSE
                    /\ pc' = [pc EXCEPT ![CLIENT] = "Done"]
                    /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                    clientCurrentUserId, 
                                    interactiveCloudCheckedId, 
                                    interactiveCloudDeliveredFirmware, 
                                    interactiveCloudFirmwareAckSent, 
                                    interactiveCloudLocationSuspended, 
                                    clientIdTrusted, serviceCloudDataReceived, 
                                    serviceCloudDataSnapshot, 
                                    gatewayInwardsOpen, gatewayFirmwareAckSent, 
                                    gatewayDeliveredFirmware, gatewayIdTrusted, 
                                    otFirmwareAckSent, otLatestData, 
                                    otDataSentToServiceCloud, otDataSigned, 
                                    otStorage, otDataRedirected, 
                                    otDataTransmissionBlocked, 
                                    otInstalledFirmware, 
                                    otUsbUnauthorisedAccess, clientFirmware, 
                                    controlNetworkDataSendToOT, 
                                    controlNetworkLatestData, 
                                    controlNetworkDataEncrypted >>

client == ClientBegin \/ ClientSendFirmwareUpdate \/ ClientViewData
             \/ ClientAwaitingIdCheck \/ ClientAwaitingFirmwareAck
             \/ ClientUpdateData

ServiceCloudBegin == /\ pc[SERVICE_CLOUD] = "ServiceCloudBegin"
                     /\ otDataSentToServiceCloud \/ DataDeliveryTimeElapsed
                     /\ IF DataDeliveryTimeElapsed
                           THEN /\ otDataTransmissionBlocked' = TRUE
                                /\ pc' = [pc EXCEPT ![SERVICE_CLOUD] = "ServiceCloudDone"]
                           ELSE /\ pc' = [pc EXCEPT ![SERVICE_CLOUD] = "ServiceCloudReceiveData"]
                                /\ UNCHANGED otDataTransmissionBlocked
                     /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                     clientCurrentUserId, 
                                     interactiveCloudCheckedId, 
                                     interactiveCloudDeliveredFirmware, 
                                     interactiveCloudFirmwareAckSent, 
                                     interactiveCloudLocationSuspended, 
                                     clientIdTrusted, serviceCloudDataReceived, 
                                     serviceCloudDataSnapshot, 
                                     gatewayInwardsOpen, 
                                     gatewayFirmwareAckSent, 
                                     gatewayDeliveredFirmware, 
                                     gatewayIdTrusted, otFirmwareAckSent, 
                                     otLatestData, otDataSentToServiceCloud, 
                                     otDataSigned, otStorage, otDataRedirected, 
                                     otInstalledFirmware, 
                                     otUsbUnauthorisedAccess, cloudDataSent, 
                                     clientFirmware, 
                                     controlNetworkDataSendToOT, 
                                     controlNetworkLatestData, 
                                     controlNetworkDataEncrypted, clientData >>

ServiceCloudReceiveData == /\ pc[SERVICE_CLOUD] = "ServiceCloudReceiveData"
                           /\ LET oldData == serviceCloudDataSnapshot IN
                                /\ IF otDataSigned /\ gatewayIdTrusted
                                      THEN /\ serviceCloudDataSnapshot' = otLatestData
                                      ELSE /\ TRUE
                                           /\ UNCHANGED serviceCloudDataSnapshot
                                /\ Assert((~otDataSigned) => (serviceCloudDataSnapshot' = oldData), 
                                          "Failure of assertion at line 222, column 17.")
                                /\ serviceCloudDataReceived' = TRUE
                                /\ otDataSentToServiceCloud' = FALSE
                           /\ pc' = [pc EXCEPT ![SERVICE_CLOUD] = "ServiceCloudEndCycle"]
                           /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                           clientCurrentUserId, 
                                           interactiveCloudCheckedId, 
                                           interactiveCloudDeliveredFirmware, 
                                           interactiveCloudFirmwareAckSent, 
                                           interactiveCloudLocationSuspended, 
                                           clientIdTrusted, gatewayInwardsOpen, 
                                           gatewayFirmwareAckSent, 
                                           gatewayDeliveredFirmware, 
                                           gatewayIdTrusted, otFirmwareAckSent, 
                                           otLatestData, otDataSigned, 
                                           otStorage, otDataRedirected, 
                                           otDataTransmissionBlocked, 
                                           otInstalledFirmware, 
                                           otUsbUnauthorisedAccess, 
                                           cloudDataSent, clientFirmware, 
                                           controlNetworkDataSendToOT, 
                                           controlNetworkLatestData, 
                                           controlNetworkDataEncrypted, 
                                           clientData >>

ServiceCloudEndCycle == /\ pc[SERVICE_CLOUD] = "ServiceCloudEndCycle"
                        /\ pc' = [pc EXCEPT ![SERVICE_CLOUD] = "ServiceCloudBegin"]
                        /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                        clientCurrentUserId, 
                                        interactiveCloudCheckedId, 
                                        interactiveCloudDeliveredFirmware, 
                                        interactiveCloudFirmwareAckSent, 
                                        interactiveCloudLocationSuspended, 
                                        clientIdTrusted, 
                                        serviceCloudDataReceived, 
                                        serviceCloudDataSnapshot, 
                                        gatewayInwardsOpen, 
                                        gatewayFirmwareAckSent, 
                                        gatewayDeliveredFirmware, 
                                        gatewayIdTrusted, otFirmwareAckSent, 
                                        otLatestData, otDataSentToServiceCloud, 
                                        otDataSigned, otStorage, 
                                        otDataRedirected, 
                                        otDataTransmissionBlocked, 
                                        otInstalledFirmware, 
                                        otUsbUnauthorisedAccess, cloudDataSent, 
                                        clientFirmware, 
                                        controlNetworkDataSendToOT, 
                                        controlNetworkLatestData, 
                                        controlNetworkDataEncrypted, 
                                        clientData >>

ServiceCloudDone == /\ pc[SERVICE_CLOUD] = "ServiceCloudDone"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![SERVICE_CLOUD] = "Done"]
                    /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                    clientCurrentUserId, 
                                    interactiveCloudCheckedId, 
                                    interactiveCloudDeliveredFirmware, 
                                    interactiveCloudFirmwareAckSent, 
                                    interactiveCloudLocationSuspended, 
                                    clientIdTrusted, serviceCloudDataReceived, 
                                    serviceCloudDataSnapshot, 
                                    gatewayInwardsOpen, gatewayFirmwareAckSent, 
                                    gatewayDeliveredFirmware, gatewayIdTrusted, 
                                    otFirmwareAckSent, otLatestData, 
                                    otDataSentToServiceCloud, otDataSigned, 
                                    otStorage, otDataRedirected, 
                                    otDataTransmissionBlocked, 
                                    otInstalledFirmware, 
                                    otUsbUnauthorisedAccess, cloudDataSent, 
                                    clientFirmware, controlNetworkDataSendToOT, 
                                    controlNetworkLatestData, 
                                    controlNetworkDataEncrypted, clientData >>

serviceCloud == ServiceCloudBegin \/ ServiceCloudReceiveData
                   \/ ServiceCloudEndCycle \/ ServiceCloudDone

InteractiveCloudBegin == /\ pc[INTERACTIVE_CLOUD] = "InteractiveCloudBegin"
                         /\ ClientRequestSent
                         /\ IF interactiveCloudLocationSuspended
                               THEN /\ clientAuthorised' = FALSE
                                    /\ interactiveCloudCheckedId' = TRUE
                                    /\ pc' = [pc EXCEPT ![INTERACTIVE_CLOUD] = "Done"]
                                    /\ UNCHANGED interactiveCloudLocationSuspended
                               ELSE /\ IF clientIdTrusted
                                          THEN /\ clientAuthorised' = TRUE
                                               /\ interactiveCloudCheckedId' = TRUE
                                               /\ IF ClientSendingFirmware
                                                     THEN /\ pc' = [pc EXCEPT ![INTERACTIVE_CLOUD] = "InteractiveCloudAttemptSendingFirmware"]
                                                     ELSE /\ pc' = [pc EXCEPT ![INTERACTIVE_CLOUD] = "InteractiveCloudDeliverData"]
                                               /\ UNCHANGED interactiveCloudLocationSuspended
                                          ELSE /\ Assert(~interactiveCloudLocationSuspended, 
                                                         "Failure of assertion at line 270, column 13.")
                                               /\ interactiveCloudLocationSuspended' = TRUE
                                               /\ clientAuthorised' = FALSE
                                               /\ interactiveCloudCheckedId' = TRUE
                                               /\ pc' = [pc EXCEPT ![INTERACTIVE_CLOUD] = "Done"]
                         /\ UNCHANGED << clientViewingData, 
                                         clientCurrentUserId, 
                                         interactiveCloudDeliveredFirmware, 
                                         interactiveCloudFirmwareAckSent, 
                                         clientIdTrusted, 
                                         serviceCloudDataReceived, 
                                         serviceCloudDataSnapshot, 
                                         gatewayInwardsOpen, 
                                         gatewayFirmwareAckSent, 
                                         gatewayDeliveredFirmware, 
                                         gatewayIdTrusted, otFirmwareAckSent, 
                                         otLatestData, 
                                         otDataSentToServiceCloud, 
                                         otDataSigned, otStorage, 
                                         otDataRedirected, 
                                         otDataTransmissionBlocked, 
                                         otInstalledFirmware, 
                                         otUsbUnauthorisedAccess, 
                                         cloudDataSent, clientFirmware, 
                                         controlNetworkDataSendToOT, 
                                         controlNetworkLatestData, 
                                         controlNetworkDataEncrypted, 
                                         clientData >>

InteractiveCloudAttemptSendingFirmware == /\ pc[INTERACTIVE_CLOUD] = "InteractiveCloudAttemptSendingFirmware"
                                          /\ interactiveCloudDeliveredFirmware' = TRUE
                                          /\ pc' = [pc EXCEPT ![INTERACTIVE_CLOUD] = "CloudAwaitingFirmwareAck"]
                                          /\ UNCHANGED << clientAuthorised, 
                                                          clientViewingData, 
                                                          clientCurrentUserId, 
                                                          interactiveCloudCheckedId, 
                                                          interactiveCloudFirmwareAckSent, 
                                                          interactiveCloudLocationSuspended, 
                                                          clientIdTrusted, 
                                                          serviceCloudDataReceived, 
                                                          serviceCloudDataSnapshot, 
                                                          gatewayInwardsOpen, 
                                                          gatewayFirmwareAckSent, 
                                                          gatewayDeliveredFirmware, 
                                                          gatewayIdTrusted, 
                                                          otFirmwareAckSent, 
                                                          otLatestData, 
                                                          otDataSentToServiceCloud, 
                                                          otDataSigned, 
                                                          otStorage, 
                                                          otDataRedirected, 
                                                          otDataTransmissionBlocked, 
                                                          otInstalledFirmware, 
                                                          otUsbUnauthorisedAccess, 
                                                          cloudDataSent, 
                                                          clientFirmware, 
                                                          controlNetworkDataSendToOT, 
                                                          controlNetworkLatestData, 
                                                          controlNetworkDataEncrypted, 
                                                          clientData >>

CloudAwaitingFirmwareAck == /\ pc[INTERACTIVE_CLOUD] = "CloudAwaitingFirmwareAck"
                            /\ gatewayFirmwareAckSent
                            /\ pc' = [pc EXCEPT ![INTERACTIVE_CLOUD] = "InteractiveCloudRelayFirmwareAck"]
                            /\ UNCHANGED << clientAuthorised, 
                                            clientViewingData, 
                                            clientCurrentUserId, 
                                            interactiveCloudCheckedId, 
                                            interactiveCloudDeliveredFirmware, 
                                            interactiveCloudFirmwareAckSent, 
                                            interactiveCloudLocationSuspended, 
                                            clientIdTrusted, 
                                            serviceCloudDataReceived, 
                                            serviceCloudDataSnapshot, 
                                            gatewayInwardsOpen, 
                                            gatewayFirmwareAckSent, 
                                            gatewayDeliveredFirmware, 
                                            gatewayIdTrusted, 
                                            otFirmwareAckSent, otLatestData, 
                                            otDataSentToServiceCloud, 
                                            otDataSigned, otStorage, 
                                            otDataRedirected, 
                                            otDataTransmissionBlocked, 
                                            otInstalledFirmware, 
                                            otUsbUnauthorisedAccess, 
                                            cloudDataSent, clientFirmware, 
                                            controlNetworkDataSendToOT, 
                                            controlNetworkLatestData, 
                                            controlNetworkDataEncrypted, 
                                            clientData >>

InteractiveCloudRelayFirmwareAck == /\ pc[INTERACTIVE_CLOUD] = "InteractiveCloudRelayFirmwareAck"
                                    /\ interactiveCloudFirmwareAckSent' = TRUE
                                    /\ pc' = [pc EXCEPT ![INTERACTIVE_CLOUD] = "Done"]
                                    /\ UNCHANGED << clientAuthorised, 
                                                    clientViewingData, 
                                                    clientCurrentUserId, 
                                                    interactiveCloudCheckedId, 
                                                    interactiveCloudDeliveredFirmware, 
                                                    interactiveCloudLocationSuspended, 
                                                    clientIdTrusted, 
                                                    serviceCloudDataReceived, 
                                                    serviceCloudDataSnapshot, 
                                                    gatewayInwardsOpen, 
                                                    gatewayFirmwareAckSent, 
                                                    gatewayDeliveredFirmware, 
                                                    gatewayIdTrusted, 
                                                    otFirmwareAckSent, 
                                                    otLatestData, 
                                                    otDataSentToServiceCloud, 
                                                    otDataSigned, otStorage, 
                                                    otDataRedirected, 
                                                    otDataTransmissionBlocked, 
                                                    otInstalledFirmware, 
                                                    otUsbUnauthorisedAccess, 
                                                    cloudDataSent, 
                                                    clientFirmware, 
                                                    controlNetworkDataSendToOT, 
                                                    controlNetworkLatestData, 
                                                    controlNetworkDataEncrypted, 
                                                    clientData >>

InteractiveCloudDeliverData == /\ pc[INTERACTIVE_CLOUD] = "InteractiveCloudDeliverData"
                               /\ Assert(clientViewingData, 
                                         "Failure of assertion at line 264, column 21.")
                               /\ cloudDataSent' = TRUE
                               /\ pc' = [pc EXCEPT ![INTERACTIVE_CLOUD] = "Done"]
                               /\ UNCHANGED << clientAuthorised, 
                                               clientViewingData, 
                                               clientCurrentUserId, 
                                               interactiveCloudCheckedId, 
                                               interactiveCloudDeliveredFirmware, 
                                               interactiveCloudFirmwareAckSent, 
                                               interactiveCloudLocationSuspended, 
                                               clientIdTrusted, 
                                               serviceCloudDataReceived, 
                                               serviceCloudDataSnapshot, 
                                               gatewayInwardsOpen, 
                                               gatewayFirmwareAckSent, 
                                               gatewayDeliveredFirmware, 
                                               gatewayIdTrusted, 
                                               otFirmwareAckSent, otLatestData, 
                                               otDataSentToServiceCloud, 
                                               otDataSigned, otStorage, 
                                               otDataRedirected, 
                                               otDataTransmissionBlocked, 
                                               otInstalledFirmware, 
                                               otUsbUnauthorisedAccess, 
                                               clientFirmware, 
                                               controlNetworkDataSendToOT, 
                                               controlNetworkLatestData, 
                                               controlNetworkDataEncrypted, 
                                               clientData >>

interactiveCloud == InteractiveCloudBegin
                       \/ InteractiveCloudAttemptSendingFirmware
                       \/ CloudAwaitingFirmwareAck
                       \/ InteractiveCloudRelayFirmwareAck
                       \/ InteractiveCloudDeliverData

GatewayAwaitingFirmware == /\ pc[GATEWAY] = "GatewayAwaitingFirmware"
                           /\ interactiveCloudDeliveredFirmware \/ pc[INTERACTIVE_CLOUD] = "Done"
                           /\ IF interactiveCloudDeliveredFirmware
                                 THEN /\ \E b \in {TRUE, FALSE}:
                                           gatewayInwardsOpen' = b
                                      /\ IF gatewayInwardsOpen'
                                            THEN /\ Assert(clientAuthorised, 
                                                           "Failure of assertion at line 294, column 13.")
                                                 /\ gatewayDeliveredFirmware' = TRUE
                                                 /\ pc' = [pc EXCEPT ![GATEWAY] = "GatewayAwaitingFirmwareAck"]
                                            ELSE /\ pc' = [pc EXCEPT ![GATEWAY] = "GatewayAwaitingOT"]
                                                 /\ UNCHANGED gatewayDeliveredFirmware
                                 ELSE /\ pc' = [pc EXCEPT ![GATEWAY] = "Done"]
                                      /\ UNCHANGED << gatewayInwardsOpen, 
                                                      gatewayDeliveredFirmware >>
                           /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                           clientCurrentUserId, 
                                           interactiveCloudCheckedId, 
                                           interactiveCloudDeliveredFirmware, 
                                           interactiveCloudFirmwareAckSent, 
                                           interactiveCloudLocationSuspended, 
                                           clientIdTrusted, 
                                           serviceCloudDataReceived, 
                                           serviceCloudDataSnapshot, 
                                           gatewayFirmwareAckSent, 
                                           gatewayIdTrusted, otFirmwareAckSent, 
                                           otLatestData, 
                                           otDataSentToServiceCloud, 
                                           otDataSigned, otStorage, 
                                           otDataRedirected, 
                                           otDataTransmissionBlocked, 
                                           otInstalledFirmware, 
                                           otUsbUnauthorisedAccess, 
                                           cloudDataSent, clientFirmware, 
                                           controlNetworkDataSendToOT, 
                                           controlNetworkLatestData, 
                                           controlNetworkDataEncrypted, 
                                           clientData >>

GatewayAwaitingOT == /\ pc[GATEWAY] = "GatewayAwaitingOT"
                     /\ gatewayFirmwareAckSent' = TRUE
                     /\ pc' = [pc EXCEPT ![GATEWAY] = "Done"]
                     /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                     clientCurrentUserId, 
                                     interactiveCloudCheckedId, 
                                     interactiveCloudDeliveredFirmware, 
                                     interactiveCloudFirmwareAckSent, 
                                     interactiveCloudLocationSuspended, 
                                     clientIdTrusted, serviceCloudDataReceived, 
                                     serviceCloudDataSnapshot, 
                                     gatewayInwardsOpen, 
                                     gatewayDeliveredFirmware, 
                                     gatewayIdTrusted, otFirmwareAckSent, 
                                     otLatestData, otDataSentToServiceCloud, 
                                     otDataSigned, otStorage, otDataRedirected, 
                                     otDataTransmissionBlocked, 
                                     otInstalledFirmware, 
                                     otUsbUnauthorisedAccess, cloudDataSent, 
                                     clientFirmware, 
                                     controlNetworkDataSendToOT, 
                                     controlNetworkLatestData, 
                                     controlNetworkDataEncrypted, clientData >>

GatewayAwaitingFirmwareAck == /\ pc[GATEWAY] = "GatewayAwaitingFirmwareAck"
                              /\ otFirmwareAckSent
                              /\ pc' = [pc EXCEPT ![GATEWAY] = "GatewayAwaitingOT"]
                              /\ UNCHANGED << clientAuthorised, 
                                              clientViewingData, 
                                              clientCurrentUserId, 
                                              interactiveCloudCheckedId, 
                                              interactiveCloudDeliveredFirmware, 
                                              interactiveCloudFirmwareAckSent, 
                                              interactiveCloudLocationSuspended, 
                                              clientIdTrusted, 
                                              serviceCloudDataReceived, 
                                              serviceCloudDataSnapshot, 
                                              gatewayInwardsOpen, 
                                              gatewayFirmwareAckSent, 
                                              gatewayDeliveredFirmware, 
                                              gatewayIdTrusted, 
                                              otFirmwareAckSent, otLatestData, 
                                              otDataSentToServiceCloud, 
                                              otDataSigned, otStorage, 
                                              otDataRedirected, 
                                              otDataTransmissionBlocked, 
                                              otInstalledFirmware, 
                                              otUsbUnauthorisedAccess, 
                                              cloudDataSent, clientFirmware, 
                                              controlNetworkDataSendToOT, 
                                              controlNetworkLatestData, 
                                              controlNetworkDataEncrypted, 
                                              clientData >>

gateway == GatewayAwaitingFirmware \/ GatewayAwaitingOT
              \/ GatewayAwaitingFirmwareAck

OTBegin == /\ pc[OT] = "OTBegin"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![OT] = "OTReceiveData"]
           /\ UNCHANGED << clientAuthorised, clientViewingData, 
                           clientCurrentUserId, interactiveCloudCheckedId, 
                           interactiveCloudDeliveredFirmware, 
                           interactiveCloudFirmwareAckSent, 
                           interactiveCloudLocationSuspended, clientIdTrusted, 
                           serviceCloudDataReceived, serviceCloudDataSnapshot, 
                           gatewayInwardsOpen, gatewayFirmwareAckSent, 
                           gatewayDeliveredFirmware, gatewayIdTrusted, 
                           otFirmwareAckSent, otLatestData, 
                           otDataSentToServiceCloud, otDataSigned, otStorage, 
                           otDataRedirected, otDataTransmissionBlocked, 
                           otInstalledFirmware, otUsbUnauthorisedAccess, 
                           cloudDataSent, clientFirmware, 
                           controlNetworkDataSendToOT, 
                           controlNetworkLatestData, 
                           controlNetworkDataEncrypted, clientData >>

OTReceiveData == /\ pc[OT] = "OTReceiveData"
                 /\ controlNetworkDataSendToOT
                 /\ Assert(otLatestData /= controlNetworkLatestData, 
                           "Failure of assertion at line 314, column 9.")
                 /\ Assert(~controlNetworkDataEncrypted, 
                           "Failure of assertion at line 316, column 9.")
                 /\ otLatestData' = controlNetworkLatestData
                 /\ controlNetworkDataEncrypted' = TRUE
                 /\ controlNetworkDataSendToOT' = FALSE
                 /\ pc' = [pc EXCEPT ![OT] = "OTSendData"]
                 /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                 clientCurrentUserId, 
                                 interactiveCloudCheckedId, 
                                 interactiveCloudDeliveredFirmware, 
                                 interactiveCloudFirmwareAckSent, 
                                 interactiveCloudLocationSuspended, 
                                 clientIdTrusted, serviceCloudDataReceived, 
                                 serviceCloudDataSnapshot, gatewayInwardsOpen, 
                                 gatewayFirmwareAckSent, 
                                 gatewayDeliveredFirmware, gatewayIdTrusted, 
                                 otFirmwareAckSent, otDataSentToServiceCloud, 
                                 otDataSigned, otStorage, otDataRedirected, 
                                 otDataTransmissionBlocked, 
                                 otInstalledFirmware, otUsbUnauthorisedAccess, 
                                 cloudDataSent, clientFirmware, 
                                 controlNetworkLatestData, clientData >>

OTSendData == /\ pc[OT] = "OTSendData"
              /\ IF ~otDataTransmissionBlocked
                    THEN /\ \E b \in {TRUE, FALSE}:
                              otDataSigned' = b
                         /\ serviceCloudDataReceived' = FALSE
                         /\ \/ /\ pc' = [pc EXCEPT ![OT] = "OTSendToServiceCloud"]
                            \/ /\ pc' = [pc EXCEPT ![OT] = "OTRedirectData"]
                    ELSE /\ pc' = [pc EXCEPT ![OT] = "OTLogDataBlock"]
                         /\ UNCHANGED << serviceCloudDataReceived, 
                                         otDataSigned >>
              /\ UNCHANGED << clientAuthorised, clientViewingData, 
                              clientCurrentUserId, interactiveCloudCheckedId, 
                              interactiveCloudDeliveredFirmware, 
                              interactiveCloudFirmwareAckSent, 
                              interactiveCloudLocationSuspended, 
                              clientIdTrusted, serviceCloudDataSnapshot, 
                              gatewayInwardsOpen, gatewayFirmwareAckSent, 
                              gatewayDeliveredFirmware, gatewayIdTrusted, 
                              otFirmwareAckSent, otLatestData, 
                              otDataSentToServiceCloud, otStorage, 
                              otDataRedirected, otDataTransmissionBlocked, 
                              otInstalledFirmware, otUsbUnauthorisedAccess, 
                              cloudDataSent, clientFirmware, 
                              controlNetworkDataSendToOT, 
                              controlNetworkLatestData, 
                              controlNetworkDataEncrypted, clientData >>

OTFinishSendingData == /\ pc[OT] = "OTFinishSendingData"
                       /\ otDataRedirected' = FALSE
                       /\ pc' = [pc EXCEPT ![OT] = "OTReadUSB"]
                       /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                       clientCurrentUserId, 
                                       interactiveCloudCheckedId, 
                                       interactiveCloudDeliveredFirmware, 
                                       interactiveCloudFirmwareAckSent, 
                                       interactiveCloudLocationSuspended, 
                                       clientIdTrusted, 
                                       serviceCloudDataReceived, 
                                       serviceCloudDataSnapshot, 
                                       gatewayInwardsOpen, 
                                       gatewayFirmwareAckSent, 
                                       gatewayDeliveredFirmware, 
                                       gatewayIdTrusted, otFirmwareAckSent, 
                                       otLatestData, otDataSentToServiceCloud, 
                                       otDataSigned, otStorage, 
                                       otDataTransmissionBlocked, 
                                       otInstalledFirmware, 
                                       otUsbUnauthorisedAccess, cloudDataSent, 
                                       clientFirmware, 
                                       controlNetworkDataSendToOT, 
                                       controlNetworkLatestData, 
                                       controlNetworkDataEncrypted, clientData >>

OTLogDataBlock == /\ pc[OT] = "OTLogDataBlock"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT ![OT] = "OTReadUSB"]
                  /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                  clientCurrentUserId, 
                                  interactiveCloudCheckedId, 
                                  interactiveCloudDeliveredFirmware, 
                                  interactiveCloudFirmwareAckSent, 
                                  interactiveCloudLocationSuspended, 
                                  clientIdTrusted, serviceCloudDataReceived, 
                                  serviceCloudDataSnapshot, gatewayInwardsOpen, 
                                  gatewayFirmwareAckSent, 
                                  gatewayDeliveredFirmware, gatewayIdTrusted, 
                                  otFirmwareAckSent, otLatestData, 
                                  otDataSentToServiceCloud, otDataSigned, 
                                  otStorage, otDataRedirected, 
                                  otDataTransmissionBlocked, 
                                  otInstalledFirmware, otUsbUnauthorisedAccess, 
                                  cloudDataSent, clientFirmware, 
                                  controlNetworkDataSendToOT, 
                                  controlNetworkLatestData, 
                                  controlNetworkDataEncrypted, clientData >>

OTSendToServiceCloud == /\ pc[OT] = "OTSendToServiceCloud"
                        /\ otDataSentToServiceCloud' = TRUE
                        /\ Assert(~otDataRedirected, 
                                  "Failure of assertion at line 330, column 17.")
                        /\ pc' = [pc EXCEPT ![OT] = "OTAwaitingServiceCloud"]
                        /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                        clientCurrentUserId, 
                                        interactiveCloudCheckedId, 
                                        interactiveCloudDeliveredFirmware, 
                                        interactiveCloudFirmwareAckSent, 
                                        interactiveCloudLocationSuspended, 
                                        clientIdTrusted, 
                                        serviceCloudDataReceived, 
                                        serviceCloudDataSnapshot, 
                                        gatewayInwardsOpen, 
                                        gatewayFirmwareAckSent, 
                                        gatewayDeliveredFirmware, 
                                        gatewayIdTrusted, otFirmwareAckSent, 
                                        otLatestData, otDataSigned, otStorage, 
                                        otDataRedirected, 
                                        otDataTransmissionBlocked, 
                                        otInstalledFirmware, 
                                        otUsbUnauthorisedAccess, cloudDataSent, 
                                        clientFirmware, 
                                        controlNetworkDataSendToOT, 
                                        controlNetworkLatestData, 
                                        controlNetworkDataEncrypted, 
                                        clientData >>

OTAwaitingServiceCloud == /\ pc[OT] = "OTAwaitingServiceCloud"
                          /\ serviceCloudDataReceived
                          /\ pc' = [pc EXCEPT ![OT] = "OTFinishSendingData"]
                          /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                          clientCurrentUserId, 
                                          interactiveCloudCheckedId, 
                                          interactiveCloudDeliveredFirmware, 
                                          interactiveCloudFirmwareAckSent, 
                                          interactiveCloudLocationSuspended, 
                                          clientIdTrusted, 
                                          serviceCloudDataReceived, 
                                          serviceCloudDataSnapshot, 
                                          gatewayInwardsOpen, 
                                          gatewayFirmwareAckSent, 
                                          gatewayDeliveredFirmware, 
                                          gatewayIdTrusted, otFirmwareAckSent, 
                                          otLatestData, 
                                          otDataSentToServiceCloud, 
                                          otDataSigned, otStorage, 
                                          otDataRedirected, 
                                          otDataTransmissionBlocked, 
                                          otInstalledFirmware, 
                                          otUsbUnauthorisedAccess, 
                                          cloudDataSent, clientFirmware, 
                                          controlNetworkDataSendToOT, 
                                          controlNetworkLatestData, 
                                          controlNetworkDataEncrypted, 
                                          clientData >>

OTRedirectData == /\ pc[OT] = "OTRedirectData"
                  /\ otDataRedirected' = TRUE
                  /\ Assert(~otDataSentToServiceCloud, 
                            "Failure of assertion at line 335, column 17.")
                  /\ pc' = [pc EXCEPT ![OT] = "OTFinishSendingData"]
                  /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                  clientCurrentUserId, 
                                  interactiveCloudCheckedId, 
                                  interactiveCloudDeliveredFirmware, 
                                  interactiveCloudFirmwareAckSent, 
                                  interactiveCloudLocationSuspended, 
                                  clientIdTrusted, serviceCloudDataReceived, 
                                  serviceCloudDataSnapshot, gatewayInwardsOpen, 
                                  gatewayFirmwareAckSent, 
                                  gatewayDeliveredFirmware, gatewayIdTrusted, 
                                  otFirmwareAckSent, otLatestData, 
                                  otDataSentToServiceCloud, otDataSigned, 
                                  otStorage, otDataTransmissionBlocked, 
                                  otInstalledFirmware, otUsbUnauthorisedAccess, 
                                  cloudDataSent, clientFirmware, 
                                  controlNetworkDataSendToOT, 
                                  controlNetworkLatestData, 
                                  controlNetworkDataEncrypted, clientData >>

OTReadUSB == /\ pc[OT] = "OTReadUSB"
             /\ \/ /\ pc' = [pc EXCEPT ![OT] = "OTUSBConnected"]
                \/ /\ pc' = [pc EXCEPT ![OT] = "OTUSBNotConnected"]
             /\ UNCHANGED << clientAuthorised, clientViewingData, 
                             clientCurrentUserId, interactiveCloudCheckedId, 
                             interactiveCloudDeliveredFirmware, 
                             interactiveCloudFirmwareAckSent, 
                             interactiveCloudLocationSuspended, 
                             clientIdTrusted, serviceCloudDataReceived, 
                             serviceCloudDataSnapshot, gatewayInwardsOpen, 
                             gatewayFirmwareAckSent, gatewayDeliveredFirmware, 
                             gatewayIdTrusted, otFirmwareAckSent, otLatestData, 
                             otDataSentToServiceCloud, otDataSigned, otStorage, 
                             otDataRedirected, otDataTransmissionBlocked, 
                             otInstalledFirmware, otUsbUnauthorisedAccess, 
                             cloudDataSent, clientFirmware, 
                             controlNetworkDataSendToOT, 
                             controlNetworkLatestData, 
                             controlNetworkDataEncrypted, clientData >>

OTUSBConnected == /\ pc[OT] = "OTUSBConnected"
                  /\ \/ /\ pc' = [pc EXCEPT ![OT] = "OTPasswordOK"]
                     \/ /\ pc' = [pc EXCEPT ![OT] = "OTPasswordNotOk"]
                  /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                  clientCurrentUserId, 
                                  interactiveCloudCheckedId, 
                                  interactiveCloudDeliveredFirmware, 
                                  interactiveCloudFirmwareAckSent, 
                                  interactiveCloudLocationSuspended, 
                                  clientIdTrusted, serviceCloudDataReceived, 
                                  serviceCloudDataSnapshot, gatewayInwardsOpen, 
                                  gatewayFirmwareAckSent, 
                                  gatewayDeliveredFirmware, gatewayIdTrusted, 
                                  otFirmwareAckSent, otLatestData, 
                                  otDataSentToServiceCloud, otDataSigned, 
                                  otStorage, otDataRedirected, 
                                  otDataTransmissionBlocked, 
                                  otInstalledFirmware, otUsbUnauthorisedAccess, 
                                  cloudDataSent, clientFirmware, 
                                  controlNetworkDataSendToOT, 
                                  controlNetworkLatestData, 
                                  controlNetworkDataEncrypted, clientData >>

OTPasswordOK == /\ pc[OT] = "OTPasswordOK"
                /\ \/ /\ pc' = [pc EXCEPT ![OT] = "OTUSBHasFirmware"]
                   \/ /\ pc' = [pc EXCEPT ![OT] = "OTUSBHasNoFirmware"]
                /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                clientCurrentUserId, interactiveCloudCheckedId, 
                                interactiveCloudDeliveredFirmware, 
                                interactiveCloudFirmwareAckSent, 
                                interactiveCloudLocationSuspended, 
                                clientIdTrusted, serviceCloudDataReceived, 
                                serviceCloudDataSnapshot, gatewayInwardsOpen, 
                                gatewayFirmwareAckSent, 
                                gatewayDeliveredFirmware, gatewayIdTrusted, 
                                otFirmwareAckSent, otLatestData, 
                                otDataSentToServiceCloud, otDataSigned, 
                                otStorage, otDataRedirected, 
                                otDataTransmissionBlocked, otInstalledFirmware, 
                                otUsbUnauthorisedAccess, cloudDataSent, 
                                clientFirmware, controlNetworkDataSendToOT, 
                                controlNetworkLatestData, 
                                controlNetworkDataEncrypted, clientData >>

OTUSBHasFirmware == /\ pc[OT] = "OTUSBHasFirmware"
                    /\ \E usbFirmware \in AllFirmware:
                         LET usbFirmwareTimestamped == <<NextFirmwareTimestamp, usbFirmware>> IN
                           IF FirmwareValid(usbFirmwareTimestamped)
                              THEN /\ otStorage' = usbFirmwareTimestamped
                              ELSE /\ TRUE
                                   /\ UNCHANGED otStorage
                    /\ pc' = [pc EXCEPT ![OT] = "OTReceiveFirmware"]
                    /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                    clientCurrentUserId, 
                                    interactiveCloudCheckedId, 
                                    interactiveCloudDeliveredFirmware, 
                                    interactiveCloudFirmwareAckSent, 
                                    interactiveCloudLocationSuspended, 
                                    clientIdTrusted, serviceCloudDataReceived, 
                                    serviceCloudDataSnapshot, 
                                    gatewayInwardsOpen, gatewayFirmwareAckSent, 
                                    gatewayDeliveredFirmware, gatewayIdTrusted, 
                                    otFirmwareAckSent, otLatestData, 
                                    otDataSentToServiceCloud, otDataSigned, 
                                    otDataRedirected, 
                                    otDataTransmissionBlocked, 
                                    otInstalledFirmware, 
                                    otUsbUnauthorisedAccess, cloudDataSent, 
                                    clientFirmware, controlNetworkDataSendToOT, 
                                    controlNetworkLatestData, 
                                    controlNetworkDataEncrypted, clientData >>

OTUSBHasNoFirmware == /\ pc[OT] = "OTUSBHasNoFirmware"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT ![OT] = "OTReceiveFirmware"]
                      /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                      clientCurrentUserId, 
                                      interactiveCloudCheckedId, 
                                      interactiveCloudDeliveredFirmware, 
                                      interactiveCloudFirmwareAckSent, 
                                      interactiveCloudLocationSuspended, 
                                      clientIdTrusted, 
                                      serviceCloudDataReceived, 
                                      serviceCloudDataSnapshot, 
                                      gatewayInwardsOpen, 
                                      gatewayFirmwareAckSent, 
                                      gatewayDeliveredFirmware, 
                                      gatewayIdTrusted, otFirmwareAckSent, 
                                      otLatestData, otDataSentToServiceCloud, 
                                      otDataSigned, otStorage, 
                                      otDataRedirected, 
                                      otDataTransmissionBlocked, 
                                      otInstalledFirmware, 
                                      otUsbUnauthorisedAccess, cloudDataSent, 
                                      clientFirmware, 
                                      controlNetworkDataSendToOT, 
                                      controlNetworkLatestData, 
                                      controlNetworkDataEncrypted, clientData >>

OTPasswordNotOk == /\ pc[OT] = "OTPasswordNotOk"
                   /\ otUsbUnauthorisedAccess' = TRUE
                   /\ pc' = [pc EXCEPT ![OT] = "OTUsbSecurityEventReset"]
                   /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                   clientCurrentUserId, 
                                   interactiveCloudCheckedId, 
                                   interactiveCloudDeliveredFirmware, 
                                   interactiveCloudFirmwareAckSent, 
                                   interactiveCloudLocationSuspended, 
                                   clientIdTrusted, serviceCloudDataReceived, 
                                   serviceCloudDataSnapshot, 
                                   gatewayInwardsOpen, gatewayFirmwareAckSent, 
                                   gatewayDeliveredFirmware, gatewayIdTrusted, 
                                   otFirmwareAckSent, otLatestData, 
                                   otDataSentToServiceCloud, otDataSigned, 
                                   otStorage, otDataRedirected, 
                                   otDataTransmissionBlocked, 
                                   otInstalledFirmware, cloudDataSent, 
                                   clientFirmware, controlNetworkDataSendToOT, 
                                   controlNetworkLatestData, 
                                   controlNetworkDataEncrypted, clientData >>

OTUsbSecurityEventReset == /\ pc[OT] = "OTUsbSecurityEventReset"
                           /\ otUsbUnauthorisedAccess' = FALSE
                           /\ pc' = [pc EXCEPT ![OT] = "OTReceiveFirmware"]
                           /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                           clientCurrentUserId, 
                                           interactiveCloudCheckedId, 
                                           interactiveCloudDeliveredFirmware, 
                                           interactiveCloudFirmwareAckSent, 
                                           interactiveCloudLocationSuspended, 
                                           clientIdTrusted, 
                                           serviceCloudDataReceived, 
                                           serviceCloudDataSnapshot, 
                                           gatewayInwardsOpen, 
                                           gatewayFirmwareAckSent, 
                                           gatewayDeliveredFirmware, 
                                           gatewayIdTrusted, otFirmwareAckSent, 
                                           otLatestData, 
                                           otDataSentToServiceCloud, 
                                           otDataSigned, otStorage, 
                                           otDataRedirected, 
                                           otDataTransmissionBlocked, 
                                           otInstalledFirmware, cloudDataSent, 
                                           clientFirmware, 
                                           controlNetworkDataSendToOT, 
                                           controlNetworkLatestData, 
                                           controlNetworkDataEncrypted, 
                                           clientData >>

OTUSBNotConnected == /\ pc[OT] = "OTUSBNotConnected"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![OT] = "OTReceiveFirmware"]
                     /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                     clientCurrentUserId, 
                                     interactiveCloudCheckedId, 
                                     interactiveCloudDeliveredFirmware, 
                                     interactiveCloudFirmwareAckSent, 
                                     interactiveCloudLocationSuspended, 
                                     clientIdTrusted, serviceCloudDataReceived, 
                                     serviceCloudDataSnapshot, 
                                     gatewayInwardsOpen, 
                                     gatewayFirmwareAckSent, 
                                     gatewayDeliveredFirmware, 
                                     gatewayIdTrusted, otFirmwareAckSent, 
                                     otLatestData, otDataSentToServiceCloud, 
                                     otDataSigned, otStorage, otDataRedirected, 
                                     otDataTransmissionBlocked, 
                                     otInstalledFirmware, 
                                     otUsbUnauthorisedAccess, cloudDataSent, 
                                     clientFirmware, 
                                     controlNetworkDataSendToOT, 
                                     controlNetworkLatestData, 
                                     controlNetworkDataEncrypted, clientData >>

OTReceiveFirmware == /\ pc[OT] = "OTReceiveFirmware"
                     /\ IF gatewayDeliveredFirmware
                           THEN /\ IF FirmwareValid(clientFirmware)
                                      THEN /\ otStorage' = clientFirmware
                                      ELSE /\ TRUE
                                           /\ UNCHANGED otStorage
                                /\ pc' = [pc EXCEPT ![OT] = "OTSendAck"]
                           ELSE /\ pc' = [pc EXCEPT ![OT] = "OTHandlePendingRequests"]
                                /\ UNCHANGED otStorage
                     /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                     clientCurrentUserId, 
                                     interactiveCloudCheckedId, 
                                     interactiveCloudDeliveredFirmware, 
                                     interactiveCloudFirmwareAckSent, 
                                     interactiveCloudLocationSuspended, 
                                     clientIdTrusted, serviceCloudDataReceived, 
                                     serviceCloudDataSnapshot, 
                                     gatewayInwardsOpen, 
                                     gatewayFirmwareAckSent, 
                                     gatewayDeliveredFirmware, 
                                     gatewayIdTrusted, otFirmwareAckSent, 
                                     otLatestData, otDataSentToServiceCloud, 
                                     otDataSigned, otDataRedirected, 
                                     otDataTransmissionBlocked, 
                                     otInstalledFirmware, 
                                     otUsbUnauthorisedAccess, cloudDataSent, 
                                     clientFirmware, 
                                     controlNetworkDataSendToOT, 
                                     controlNetworkLatestData, 
                                     controlNetworkDataEncrypted, clientData >>

OTSendAck == /\ pc[OT] = "OTSendAck"
             /\ otFirmwareAckSent' = TRUE
             /\ interactiveCloudDeliveredFirmware' = FALSE
             /\ gatewayDeliveredFirmware' = FALSE
             /\ pc' = [pc EXCEPT ![OT] = "OTHandlePendingRequests"]
             /\ UNCHANGED << clientAuthorised, clientViewingData, 
                             clientCurrentUserId, interactiveCloudCheckedId, 
                             interactiveCloudFirmwareAckSent, 
                             interactiveCloudLocationSuspended, 
                             clientIdTrusted, serviceCloudDataReceived, 
                             serviceCloudDataSnapshot, gatewayInwardsOpen, 
                             gatewayFirmwareAckSent, gatewayIdTrusted, 
                             otLatestData, otDataSentToServiceCloud, 
                             otDataSigned, otStorage, otDataRedirected, 
                             otDataTransmissionBlocked, otInstalledFirmware, 
                             otUsbUnauthorisedAccess, cloudDataSent, 
                             clientFirmware, controlNetworkDataSendToOT, 
                             controlNetworkLatestData, 
                             controlNetworkDataEncrypted, clientData >>

OTHandlePendingRequests == /\ pc[OT] = "OTHandlePendingRequests"
                           /\ pc' = [pc EXCEPT ![OT] = "OTBegin"]
                           /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                           clientCurrentUserId, 
                                           interactiveCloudCheckedId, 
                                           interactiveCloudDeliveredFirmware, 
                                           interactiveCloudFirmwareAckSent, 
                                           interactiveCloudLocationSuspended, 
                                           clientIdTrusted, 
                                           serviceCloudDataReceived, 
                                           serviceCloudDataSnapshot, 
                                           gatewayInwardsOpen, 
                                           gatewayFirmwareAckSent, 
                                           gatewayDeliveredFirmware, 
                                           gatewayIdTrusted, otFirmwareAckSent, 
                                           otLatestData, 
                                           otDataSentToServiceCloud, 
                                           otDataSigned, otStorage, 
                                           otDataRedirected, 
                                           otDataTransmissionBlocked, 
                                           otInstalledFirmware, 
                                           otUsbUnauthorisedAccess, 
                                           cloudDataSent, clientFirmware, 
                                           controlNetworkDataSendToOT, 
                                           controlNetworkLatestData, 
                                           controlNetworkDataEncrypted, 
                                           clientData >>

ot == OTBegin \/ OTReceiveData \/ OTSendData \/ OTFinishSendingData
         \/ OTLogDataBlock \/ OTSendToServiceCloud
         \/ OTAwaitingServiceCloud \/ OTRedirectData \/ OTReadUSB
         \/ OTUSBConnected \/ OTPasswordOK \/ OTUSBHasFirmware
         \/ OTUSBHasNoFirmware \/ OTPasswordNotOk
         \/ OTUsbSecurityEventReset \/ OTUSBNotConnected
         \/ OTReceiveFirmware \/ OTSendAck \/ OTHandlePendingRequests

ControlNetworkBegin == /\ pc[CONTROL_NETWORK] = "ControlNetworkBegin"
                       /\ TRUE
                       /\ pc' = [pc EXCEPT ![CONTROL_NETWORK] = "ControlNetworkSendData"]
                       /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                       clientCurrentUserId, 
                                       interactiveCloudCheckedId, 
                                       interactiveCloudDeliveredFirmware, 
                                       interactiveCloudFirmwareAckSent, 
                                       interactiveCloudLocationSuspended, 
                                       clientIdTrusted, 
                                       serviceCloudDataReceived, 
                                       serviceCloudDataSnapshot, 
                                       gatewayInwardsOpen, 
                                       gatewayFirmwareAckSent, 
                                       gatewayDeliveredFirmware, 
                                       gatewayIdTrusted, otFirmwareAckSent, 
                                       otLatestData, otDataSentToServiceCloud, 
                                       otDataSigned, otStorage, 
                                       otDataRedirected, 
                                       otDataTransmissionBlocked, 
                                       otInstalledFirmware, 
                                       otUsbUnauthorisedAccess, cloudDataSent, 
                                       clientFirmware, 
                                       controlNetworkDataSendToOT, 
                                       controlNetworkLatestData, 
                                       controlNetworkDataEncrypted, clientData >>

ControlNetworkSendData == /\ pc[CONTROL_NETWORK] = "ControlNetworkSendData"
                          /\ controlNetworkDataEncrypted' = FALSE
                          /\ controlNetworkLatestData' = ~controlNetworkLatestData
                          /\ controlNetworkDataSendToOT' = TRUE
                          /\ pc' = [pc EXCEPT ![CONTROL_NETWORK] = "ControlNetworkAwaitingOT"]
                          /\ UNCHANGED << clientAuthorised, clientViewingData, 
                                          clientCurrentUserId, 
                                          interactiveCloudCheckedId, 
                                          interactiveCloudDeliveredFirmware, 
                                          interactiveCloudFirmwareAckSent, 
                                          interactiveCloudLocationSuspended, 
                                          clientIdTrusted, 
                                          serviceCloudDataReceived, 
                                          serviceCloudDataSnapshot, 
                                          gatewayInwardsOpen, 
                                          gatewayFirmwareAckSent, 
                                          gatewayDeliveredFirmware, 
                                          gatewayIdTrusted, otFirmwareAckSent, 
                                          otLatestData, 
                                          otDataSentToServiceCloud, 
                                          otDataSigned, otStorage, 
                                          otDataRedirected, 
                                          otDataTransmissionBlocked, 
                                          otInstalledFirmware, 
                                          otUsbUnauthorisedAccess, 
                                          cloudDataSent, clientFirmware, 
                                          clientData >>

ControlNetworkAwaitingOT == /\ pc[CONTROL_NETWORK] = "ControlNetworkAwaitingOT"
                            /\ ~controlNetworkDataSendToOT
                            /\ TRUE
                            /\ pc' = [pc EXCEPT ![CONTROL_NETWORK] = "ControlNetworkHandlePendingRequests"]
                            /\ UNCHANGED << clientAuthorised, 
                                            clientViewingData, 
                                            clientCurrentUserId, 
                                            interactiveCloudCheckedId, 
                                            interactiveCloudDeliveredFirmware, 
                                            interactiveCloudFirmwareAckSent, 
                                            interactiveCloudLocationSuspended, 
                                            clientIdTrusted, 
                                            serviceCloudDataReceived, 
                                            serviceCloudDataSnapshot, 
                                            gatewayInwardsOpen, 
                                            gatewayFirmwareAckSent, 
                                            gatewayDeliveredFirmware, 
                                            gatewayIdTrusted, 
                                            otFirmwareAckSent, otLatestData, 
                                            otDataSentToServiceCloud, 
                                            otDataSigned, otStorage, 
                                            otDataRedirected, 
                                            otDataTransmissionBlocked, 
                                            otInstalledFirmware, 
                                            otUsbUnauthorisedAccess, 
                                            cloudDataSent, clientFirmware, 
                                            controlNetworkDataSendToOT, 
                                            controlNetworkLatestData, 
                                            controlNetworkDataEncrypted, 
                                            clientData >>

ControlNetworkHandlePendingRequests == /\ pc[CONTROL_NETWORK] = "ControlNetworkHandlePendingRequests"
                                       /\ pc' = [pc EXCEPT ![CONTROL_NETWORK] = "ControlNetworkBegin"]
                                       /\ UNCHANGED << clientAuthorised, 
                                                       clientViewingData, 
                                                       clientCurrentUserId, 
                                                       interactiveCloudCheckedId, 
                                                       interactiveCloudDeliveredFirmware, 
                                                       interactiveCloudFirmwareAckSent, 
                                                       interactiveCloudLocationSuspended, 
                                                       clientIdTrusted, 
                                                       serviceCloudDataReceived, 
                                                       serviceCloudDataSnapshot, 
                                                       gatewayInwardsOpen, 
                                                       gatewayFirmwareAckSent, 
                                                       gatewayDeliveredFirmware, 
                                                       gatewayIdTrusted, 
                                                       otFirmwareAckSent, 
                                                       otLatestData, 
                                                       otDataSentToServiceCloud, 
                                                       otDataSigned, otStorage, 
                                                       otDataRedirected, 
                                                       otDataTransmissionBlocked, 
                                                       otInstalledFirmware, 
                                                       otUsbUnauthorisedAccess, 
                                                       cloudDataSent, 
                                                       clientFirmware, 
                                                       controlNetworkDataSendToOT, 
                                                       controlNetworkLatestData, 
                                                       controlNetworkDataEncrypted, 
                                                       clientData >>

controlNetwork == ControlNetworkBegin \/ ControlNetworkSendData
                     \/ ControlNetworkAwaitingOT
                     \/ ControlNetworkHandlePendingRequests

Next == client \/ serviceCloud \/ interactiveCloud \/ gateway \/ ot
           \/ controlNetwork
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(client)
        /\ WF_vars(serviceCloud)
        /\ WF_vars(interactiveCloud)
        /\ WF_vars(gateway)
        /\ WF_vars(ot)
        /\ WF_vars(controlNetwork)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* All processes, except for the service cloud, operations terminal and vehicle operator are expected to terminate
PartialTermination == <>(\A self \in (ProcSet \ {CONTROL_NETWORK, OT, SERVICE_CLOUD}): pc[self] = "Done")

\* A authorised client that sends firmware will always receive an acknowledgement from the cloud
FirmwareAcknowledgementReceivedByClient == []( (ClientSendingFirmware /\ clientAuthorised) => <>(interactiveCloudFirmwareAckSent))

\* TODO: Ensure that non-authorised client cannot view data

\* The client, cloud and gateway are guaranteed to receive acknowledgements once the gateway has delivered the firmware to the operations terminal
FirmwareAcknowledgementsReceived == [](gatewayDeliveredFirmware => <>(interactiveCloudFirmwareAckSent /\ gatewayFirmwareAckSent /\otFirmwareAckSent))

\* Delivered firmware will eventually be processed by the operations terminal
DeliveredFirmwareProcessed == [](gatewayDeliveredFirmware => <>(~interactiveCloudDeliveredFirmware /\ ~gatewayDeliveredFirmware))

\* The client firmware must contain a valid option
ValidFirmwareOptions == []( (~ClientSendingFirmware => (clientFirmware = NO_FIRMWARE)) /\
                            (ClientSendingFirmware => (clientFirmware[FirmwareValueIndex] \in AllFirmware)))

\* The operations terminal must only accept valid firmware
OTFirmwareAlwaysValid == []( FirmwareValid(otInstalledFirmware) /\ (otStorage /= NO_FIRMWARE => FirmwareValid(otStorage)) )

\* The operations terminal must have firmware installed at all times
OTFirmwareAlwaysInstalled == [](otInstalledFirmware /= NO_FIRMWARE)

\* The firmware backup is the oldest piece of firmware that exists
BackupFirmwareAlwaysOlder == []( (otStorage /= NO_FIRMWARE) => (otStorage[FirmwareTimestampIndex] > otInstalledFirmware[FirmwareTimestampIndex]) )

\* Unauthorised USB usage must be logged
UnauthorisedUSBUsageLogged == []( (pc[OT] = "OTPasswordNotOk") => <>(otUsbUnauthorisedAccess) )

\* 'otUsbUnauthorisedAccess' must be reset every operations terminal cycle
UnauthorisedUSBUsageEventReset == []( (pc[OT] = "OTBegin") => otUsbUnauthorisedAccess = FALSE )

DataBlockLogged == [](otDataTransmissionBlocked => []<>(pc[OT] = "OTLogDataBlock"))

InvalidIdsRejected == []( ~clientIdTrusted => <>[](~clientAuthorised) )

LocationGetSuspended == []( ~clientIdTrusted => <>[](interactiveCloudLocationSuspended) )

OTEncryptsControlNetworkData == [](<>(controlNetworkDataEncrypted))

UserIdExists == [](clientAuthorised => clientCurrentUserId /= NO_USER) 

=============================================================================
