import 'package:flutter/material.dart';

import 'package:camera_techcase/src/widgets/picture_confirm_overlay.dart';
import 'package:camera_techcase/src/widgets/top_app_bar.dart';
import 'package:camera/camera.dart';

class ConfirmScreen extends StatelessWidget {
  const ConfirmScreen(this.uploadPicture, {super.key});

  final XFile uploadPicture;

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: const CustomAppBar(title: "SAVE A PICTURE"),
      body: SizedBox(
        height: MediaQuery.of(context).size.height,
        child: SingleChildScrollView(
          child: Center(
            child: PictureConfirmOverlay(uploadPicture: uploadPicture)
          ),
        ),
      ),
    );
  }
}