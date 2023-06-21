import 'package:camera/camera.dart';
import 'package:flutter/material.dart';
import 'package:flutter/cupertino.dart';
import 'package:go_router/go_router.dart';

class CameraPage extends StatefulWidget {
  const CameraPage({Key? key}) : super(key: key);

  @override
  State<CameraPage> createState() => _CameraPageState();
}

class _CameraPageState extends State<CameraPage> {
  CameraController? _cameraController;
  bool _isRearCameraSelected = true;

  List<CameraDescription> _availableCameras = [];

  @override
  void dispose() {
    _cameraController?.dispose();
    super.dispose();
  }

  @override
  void initState() {
    super.initState();
    _getAvailableCameras();
  }

  Future<void> _getAvailableCameras() async {
    WidgetsFlutterBinding.ensureInitialized();
    _availableCameras = await availableCameras();
    initCamera(_availableCameras[0]);
  }

  Future<XFile?> takePicture() async {
    if (!_cameraController!.value.isInitialized) {
      return null;
    }

    if (_cameraController!.value.isTakingPicture) {
      return null;
    }

    try {
      await _cameraController!.setFlashMode(FlashMode.off);
      XFile picture = await _cameraController!.takePicture();
      return picture;
    } on CameraException catch (e) {
      debugPrint('Error occured while taking picture: $e');
      return null;
    }
  }

  Future initCamera(CameraDescription cameraDescription) async {
    _cameraController = CameraController(cameraDescription, ResolutionPreset.max);
    try {
      await _cameraController!.initialize().then((_) {
        if (!mounted) return;
        setState(() {});
      });
    } on CameraException catch (e) {
      debugPrint("camera error $e");
    }
  }

  @override
  Widget build(BuildContext context) {
    if (_cameraController == null) {
      return const Center(
        child: SizedBox(
            height: 50,
            width: 50,
            child: CircularProgressIndicator()
        ),
      );
    }

    return Scaffold(
      body: SafeArea(
        child: Stack(
          children: [
            (_cameraController!.value.isInitialized)
                ? CameraPreview(_cameraController!)
                : Container(
                color: Colors.black,
                child: const Center(
                  child: CircularProgressIndicator()
                )
            ),
            Align(
              alignment: Alignment.bottomCenter,
              child: Container(
                height: MediaQuery.of(context).size.height * 0.20,
                decoration: const BoxDecoration(
                  borderRadius: BorderRadius.vertical(
                    top: Radius.circular(24)
                  ),
                  color: Colors.black
                ),
                child: Row(
                  crossAxisAlignment: CrossAxisAlignment.center,
                  children: [
                    Expanded(
                      child: IconButton(
                        padding: EdgeInsets.zero,
                        iconSize: 30,
                        icon: Icon(
                            _isRearCameraSelected
                                ? CupertinoIcons.switch_camera
                                : CupertinoIcons.switch_camera_solid,
                            color: Colors.white
                        ),
                        onPressed: () {
                          setState(() => _isRearCameraSelected = !_isRearCameraSelected);
                          initCamera(_availableCameras[_isRearCameraSelected ? 0 : 1]);
                        },
                      )
                    ),
                    Expanded(
                      child: IconButton(
                        onPressed: () async {
                          XFile? image = await takePicture();
                          if (!mounted) {
                            return;
                          }

                          GoRouter.of(context).go('/camera/save', extra: image!);
                        },
                        iconSize: 50,
                        padding: EdgeInsets.zero,
                        constraints: const BoxConstraints(),
                        icon: const Icon(
                          Icons.circle,
                          color: Colors.white
                        ),
                      )
                    ),
                    const Spacer(),
                  ]
                )
              )
            ),
          ]
        ),
      )
    );
  }
}
