import 'dart:typed_data';
import 'package:flutter/material.dart';

import 'package:camera_techcase/src/widgets/image_viewer.dart';
import 'package:camera_techcase/src/widgets/top_app_bar.dart';

class ImageViewerScreen extends StatelessWidget {
  const ImageViewerScreen({required this.title, required this.imageData, super.key});

  final String title;
  final Uint8List imageData;

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: CustomAppBar(title: title),
      body: ImageViewer(imageData: imageData, imageSource: ImageSource.gallery),
    );
  }
}